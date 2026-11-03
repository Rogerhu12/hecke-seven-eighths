import ExpansionDetector.IdealMellinIdentity
import ExpansionDetector.ExponentialTail

/-! The exponential terminal error for the genuine ideal Moebius
convolution. All coefficients and cutoffs are the same as in the finite
source; the estimate uses only the actual norm-zeta sum at exponent two. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open scoped NumberField Classical BigOperators nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]

theorem actualIdeal_terminal_remainder_bound
    (w : Ideal (𝓞 K) →*₀ ℂ) (hw : ∀ I, ‖w I‖ ≤ 1)
    (V T : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVc : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (hTc : ∀ x : ℝ, 0 ≤ x → ‖1 - T x‖ ≤ 1)
    (hTsmall : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y H : ℝ) (hD : 0 < D) (hY : 0 < Y) (hH : 0 < H)
    (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ))) :
    Summable (terminalRemainder w V T D H
      (fun q => (q : ℂ) ^ (-s) * (Real.exp (-(q : ℝ) / Y) : ℂ))) ∧
      ‖∑' I : Ideal (𝓞 K), terminalRemainder w V T D H
        (fun q => (q : ℂ) ^ (-s) * (Real.exp (-(q : ℝ) / Y) : ℂ)) I‖ ≤
        (((n + 3).factorial : ℝ) * Y ^ (n + 3) / H ^ n) *
          ∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ) := by
  letI := countable_integralIdeals (K := K)
  let a : NonzeroIntegralIdeal (K := K) → ℂ := fun I => coefficient V D I.val * w I.val
  let r : NonzeroIntegralIdeal (K := K) → ℂ := fun I =>
    (1 - V (2 * nonzeroIdealNorm I / D)) * (1 - T (nonzeroIdealNorm I / H))
  have ha (I : NonzeroIntegralIdeal (K := K)) : ‖a I‖ ≤ nonzeroIdealNorm I := by
    dsimp [a]
    rw [norm_mul]
    exact (mul_le_mul (norm_coefficient_le_norm V D hV I.val) (hw I.val)
      (norm_nonneg _) (by exact_mod_cast Nat.zero_le (Ideal.absNorm I.val))).trans_eq (mul_one _)
  have hr (I : NonzeroIntegralIdeal (K := K)) : ‖r I‖ ≤ 1 := by
    dsimp [r]
    rw [norm_mul]
    have hN := (nonzeroIdealNorm_pos I).le
    exact (mul_le_mul (hVc _ (div_nonneg (mul_nonneg (by norm_num) hN) hD.le))
      (hTc _ (div_nonneg hN hH.le)) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
  have hrzero (I : NonzeroIntegralIdeal (K := K)) (hI : nonzeroIdealNorm I ≤ H) : r I = 0 := by
    have ht := hTsmall (nonzeroIdealNorm I / H)
      (div_nonneg (nonzeroIdealNorm_pos I).le hH.le) ((div_le_one hH).mpr hI)
    simp only [r, ht, sub_self, mul_zero]
  have hb := ExpansionDetector.Analytic.exponential_terminal_tsum_bound
    nonzeroIdealNorm a r s Y H n one_le_nonzeroIdealNorm ha hr hrzero hs hY hH hzeta
  let f : Ideal (𝓞 K) → ℂ := terminalRemainder w V T D H
    (fun q => (q : ℂ) ^ (-s) * (Real.exp (-(q : ℝ) / Y) : ℂ))
  have hsup : Function.support f ⊆ (Ideal (𝓞 K))⁰ := by
    apply support_subset_nonzero_of_zero
    simp only [f, terminalRemainder, smoothedTerm, map_zero, mul_zero, zero_mul]
  have heq (I : NonzeroIntegralIdeal (K := K)) :
      a I * (nonzeroIdealNorm I : ℂ) ^ (-s) *
        (Real.exp (-nonzeroIdealNorm I / Y) : ℂ) * r I = f I.val := by
    simp only [a, r, nonzeroIdealNorm, f, terminalRemainder, smoothedTerm, Complex.ofReal_natCast]
    ring
  have hsNZ : Summable (fun I : NonzeroIntegralIdeal (K := K) => f I.val) := hb.1.congr heq
  refine ⟨((hasSum_subtype_iff_of_support_subset hsup).mp hsNZ.hasSum).summable, ?_⟩
  have ht : (∑' I : NonzeroIntegralIdeal (K := K),
      a I * (nonzeroIdealNorm I : ℂ) ^ (-s) *
        (Real.exp (-nonzeroIdealNorm I / Y) : ℂ) * r I) = ∑' I : Ideal (𝓞 K), f I := by
    calc
      _ = ∑' I : NonzeroIntegralIdeal (K := K), f I.val := tsum_congr heq
      _ = _ := tsum_subtype_eq_of_support_subset hsup
  simpa only [ht] using hb.2

end ExpansionDetector.IdealCutoff
