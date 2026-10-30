import HeckeGeneral.Analysis.ArchimedeanGammaVertical
import HeckeGeneral.Analysis.GlobalThetaData

/-! Polynomial growth of the archimedean Gamma quotients `Γ(β+z)/Γ(β-z)` on
vertical strips `σlo ≤ Re z ≤ Λ` with `σlo > -β`; the exponent is sharp
(`|τ|^{2σ}`). -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open HeckeGeneral.Analysis
open scoped Classical ComplexConjugate

theorem gamma_add_nat_prod (z : ℂ) (hz : z.im ≠ 0) (N : ℕ) :
    Complex.Gamma (z + N) = (∏ k ∈ Finset.range N, (z + k)) * Complex.Gamma z := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hne : z + N ≠ 0 := by
      intro h
      apply hz
      have := congrArg Complex.im h
      simpa using this
    rw [Finset.prod_range_succ, show z + ((N + 1 : ℕ) : ℂ) = (z + N) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

theorem norm_Gamma_quot_bound {β σlo Λ : ℝ} (hβ : 0 < β) (hlo : -β < σlo) (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ τ : ℝ, σlo ≤ σ → σ ≤ Λ → 1 / 2 ≤ |τ| →
      ‖Complex.Gamma (((β + σ : ℝ) : ℂ) + Complex.I * τ) /
        Complex.Gamma (((β - σ : ℝ) : ℂ) + Complex.I * τ)‖ ≤ C * |τ| ^ (2 * σ) := by
  set N : ℕ := ⌈Λ⌉₊ + 1 with hN
  set A : ℝ := β + |Λ| + |σlo| + N with hA
  have hNΛ : Λ ≤ (⌈Λ⌉₊ : ℝ) := Nat.le_ceil Λ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNc : (N : ℝ) = (⌈Λ⌉₊ : ℝ) + 1 := by rw [hN]; push_cast; ring
  set D : ℝ := 1 + 2 * (β + |Λ| + |σlo| + N) with hD
  have hD1 : 1 ≤ D := by rw [hD]; have := abs_nonneg Λ; have := abs_nonneg σlo; nlinarith
  refine ⟨D ^ N * Real.exp (4 * gammaVerticalStripConstant A * (2 * (|Λ| + |σlo|) + N)), by positivity, ?_⟩
  intro σ τ hσlo hσΛ hτ
  have hτ0 : 0 < |τ| := lt_of_lt_of_le (by norm_num) hτ
  set a : ℝ := β - σ with ha
  set b : ℝ := β + σ with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have haN : 0 < a + N := by rw [ha]; nlinarith
  have hbA : b ≤ A := by
    rw [hb, hA]; have := le_abs_self σ; have h2 : σ ≤ |Λ| := le_trans hσΛ (le_abs_self Λ)
    have := abs_nonneg σlo; linarith
  have haA : a + N ≤ A := by
    rw [ha, hA]; have h2 := neg_le_abs σlo; have := abs_nonneg Λ; linarith
  have hz : (((a : ℝ) : ℂ) + Complex.I * τ).im ≠ 0 := by
    have : (((a : ℝ) : ℂ) + Complex.I * τ).im = τ := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [this]; intro h; rw [h] at hτ0; simp at hτ0
  have hprod := gamma_add_nat_prod (((a : ℝ) : ℂ) + Complex.I * τ) hz N
  have hGN : Complex.Gamma (((a + N : ℝ) : ℂ) + Complex.I * τ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using haN)
  have heq : ((a + N : ℝ) : ℂ) + Complex.I * τ = (((a : ℝ) : ℂ) + Complex.I * τ) + N := by
    push_cast; ring
  rw [heq] at hGN
  have hprod_ne : (∏ k ∈ Finset.range N, ((((a : ℝ) : ℂ) + Complex.I * τ) + k)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    apply hz
    have := congrArg Complex.im h
    simpa using this
  have hquot : Complex.Gamma (((b : ℝ) : ℂ) + Complex.I * τ) /
        Complex.Gamma (((a : ℝ) : ℂ) + Complex.I * τ) =
      (∏ k ∈ Finset.range N, ((((a : ℝ) : ℂ) + Complex.I * τ) + k)) *
        (Complex.Gamma (((b : ℝ) : ℂ) + Complex.I * τ) /
          Complex.Gamma (((a + N : ℝ) : ℂ) + Complex.I * τ)) := by
    rw [heq, hprod]
    have hG : Complex.Gamma (((a : ℝ) : ℂ) + Complex.I * τ) ≠ 0 := by
      refine Complex.Gamma_ne_zero (fun m h => hz ?_)
      have := congrArg Complex.im h
      simpa using this
    field_simp
  have hlib := (norm_Gamma_ratio_vertical_strip_bounds (a := a + N) (b := b) (A := A) (t := τ)
    haN haA hb0 hbA hτ).2
  have hτ2 : 1 / 4 ≤ τ ^ 2 := by
    have : (1 / 2 : ℝ) ^ 2 ≤ |τ| ^ 2 := pow_le_pow_left₀ (by norm_num) hτ 2
    rw [sq_abs] at this; linarith
  have hexp : Real.exp ((gammaVerticalStripConstant A / τ ^ 2) * |b - (a + N)|) ≤
      Real.exp (4 * gammaVerticalStripConstant A * (2 * (|Λ| + |σlo|) + N)) := by
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ gammaVerticalStripConstant A := by
      unfold gammaVerticalStripConstant
      have : 0 ≤ A := by rw [hA]; have := abs_nonneg Λ; have := abs_nonneg σlo; linarith
      nlinarith
    have h1 : gammaVerticalStripConstant A / τ ^ 2 ≤ 4 * gammaVerticalStripConstant A := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : |b - (a + N)| ≤ 2 * (|Λ| + |σlo|) + N := by
      have : b - (a + N) = 2 * σ - N := by rw [hb, ha]; ring
      rw [this]
      have := abs_sub (2 * σ) (N : ℝ)
      have h3 : |2 * σ| ≤ 2 * (|Λ| + |σlo|) := by
        rw [abs_mul]; norm_num
        rcases abs_cases σ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [skip; skip] <;>
          first | (have := le_abs_self Λ; have := abs_nonneg σlo; linarith)
                | (have := neg_abs_le σlo; have := abs_nonneg Λ; linarith)
      rw [abs_of_nonneg hN0] at this
      linarith
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity) |>.trans (le_of_eq (by ring))
  have hprodle : ∏ k ∈ Finset.range N, ‖(((a : ℝ) : ℂ) + Complex.I * τ) + (k : ℂ)‖ ≤ (D * |τ|) ^ N := by
    refine le_trans (Finset.prod_le_prod₀ (g := fun _ => D * |τ|) (fun _ _ => norm_nonneg _) ?_)
      (by simp)
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hk).le
    have e : (((a : ℝ) : ℂ) + Complex.I * τ) + (k : ℂ) = (((a + k : ℝ)) : ℂ) + Complex.I * τ := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have h1 : |a + k| ≤ |a| + N := (abs_add_le _ _).trans (by rw [Nat.abs_cast]; linarith)
    have h2 : |a| ≤ β + |Λ| + |σlo| := by
      rw [ha]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos hβ]
      have : |σ| ≤ |Λ| + |σlo| := by
        rcases abs_cases σ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
        · have := le_abs_self Λ; have := abs_nonneg σlo; linarith
        · have := neg_le_abs σlo; have := abs_nonneg Λ; linarith
      linarith
    rw [hD]
    nlinarith [abs_nonneg (a + k), abs_nonneg a]
  have hnorm : ‖Complex.Gamma (((β + σ : ℝ) : ℂ) + Complex.I * τ) /
        Complex.Gamma (((β - σ : ℝ) : ℂ) + Complex.I * τ)‖ =
      (∏ k ∈ Finset.range N, ‖(((a : ℝ) : ℂ) + Complex.I * τ) + (k : ℂ)‖) *
        ‖Complex.Gamma (((b : ℝ) : ℂ) + Complex.I * τ) /
          Complex.Gamma (((a + N : ℝ) : ℂ) + Complex.I * τ)‖ := by
    have := congrArg norm hquot
    rw [norm_mul, norm_prod] at this
    exact this
  rw [hnorm]
  have hpow : |τ| ^ (b - (a + N)) * |τ| ^ (N : ℝ) = |τ| ^ (2 * σ) := by
    rw [← Real.rpow_add hτ0]; congr 1; rw [hb, ha]; ring
  have hpowN : (|τ| ^ N : ℝ) = |τ| ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
  calc _ ≤ (D * |τ|) ^ N * (Real.exp ((gammaVerticalStripConstant A / τ ^ 2) * |b - (a + N)|) *
          |τ| ^ (b - (a + N))) := by
        apply mul_le_mul hprodle hlib (norm_nonneg _) (by positivity)
    _ ≤ (D * |τ|) ^ N * (Real.exp (4 * gammaVerticalStripConstant A * (2 * (|Λ| + |σlo|) + N)) *
          |τ| ^ (b - (a + N))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = D ^ N * Real.exp (4 * gammaVerticalStripConstant A * (2 * (|Λ| + |σlo|) + N)) *
          |τ| ^ (2 * σ) := by
        rw [← hpow, mul_pow, hpowN]; ring

open Complex in
theorem norm_Gamma_quot_complex_bound {β σlo Λ : ℝ} (hβ : 0 < β) (hlo : -β < σlo)
    (hΛ : σlo ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, σlo ≤ z.re → z.re ≤ Λ →
      ‖Complex.Gamma (β + z) / Complex.Gamma (β - z)‖ ≤ C * (1 + |z.im|) ^ (2 * z.re) := by
  obtain ⟨C0, hC0, h0⟩ := norm_Gamma_quot_bound hβ hlo hΛ
  have hc1 : ∀ p ∈ Set.Icc σlo Λ ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      ContinuousAt (fun p : ℝ × ℝ => Complex.Gamma (β + ((p.1 : ℂ) + p.2 * Complex.I))) p := by
    intro p hp
    have hg : ContinuousAt Complex.Gamma (β + ((p.1 : ℂ) + p.2 * Complex.I)) := by
      refine (Complex.differentiableAt_Gamma _ (fun m h => ?_)).continuousAt
      have := congrArg Complex.re h
      simp at this
      have h1 := hp.1.1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hg.comp (f := fun p : ℝ × ℝ => (β : ℂ) + ((p.1 : ℂ) + p.2 * Complex.I)) (by fun_prop)
  have hc2 : Continuous (fun p : ℝ × ℝ =>
      (Complex.Gamma (β - ((p.1 : ℂ) + p.2 * Complex.I)))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Complex.Gamma (β + ((p.1 : ℂ) + p.2 * Complex.I)) *
        (Complex.Gamma (β - ((p.1 : ℂ) + p.2 * Complex.I)))⁻¹)
      (Set.Icc σlo Λ ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2)) := fun p hp =>
    ((hc1 p hp).mul hc2.continuousAt).continuousWithinAt
  obtain ⟨C1, hC1⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  set c0 : ℝ := min 1 ((3 / 2 : ℝ) ^ (2 * σlo)) with hc0
  have hc0pos : 0 < c0 := lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
  set c2 : ℝ := (3 : ℝ) ^ (2 * |σlo|) with hc2def
  have hc2one : 1 ≤ c2 := Real.one_le_rpow (by norm_num) (by positivity)
  refine ⟨C0 * c2 + max C1 0 / c0, by positivity, ?_⟩
  intro z hz1 hz2
  set σ := z.re with hσ
  set τ := z.im with hτ
  by_cases hτ12 : 1 / 2 ≤ |τ|
  · have hq := h0 σ τ hz1 hz2 hτ12
    have hzeq : (β : ℂ) + z = ((β + σ : ℝ) : ℂ) + Complex.I * τ := by
      apply Complex.ext <;> simp [hσ, hτ]
    have hzeq2 : (β : ℂ) - z = conj (((β - σ : ℝ) : ℂ) + Complex.I * τ) := by
      apply Complex.ext <;> simp [hσ, hτ]
    have hn : ‖Complex.Gamma ((β : ℂ) + z) / Complex.Gamma ((β : ℂ) - z)‖ =
        ‖Complex.Gamma (((β + σ : ℝ) : ℂ) + Complex.I * τ) /
          Complex.Gamma (((β - σ : ℝ) : ℂ) + Complex.I * τ)‖ := by
      rw [hzeq, hzeq2, Complex.Gamma_conj, norm_div, norm_div, RCLike.norm_conj]
    rw [hn]
    have hτ0 : 0 < |τ| := lt_of_lt_of_le (by norm_num) hτ12
    have hpow : |τ| ^ (2 * σ) ≤ c2 * (1 + |τ|) ^ (2 * σ) := by
      rcases le_or_gt 0 (2 * σ) with h | h
      · calc |τ| ^ (2 * σ) ≤ (1 + |τ|) ^ (2 * σ) :=
              Real.rpow_le_rpow hτ0.le (by linarith) h
          _ = 1 * (1 + |τ|) ^ (2 * σ) := by ring
          _ ≤ c2 * (1 + |τ|) ^ (2 * σ) :=
              mul_le_mul_of_nonneg_right hc2one (by positivity)
      · have h3 : (1 + |τ|) / 3 ≤ |τ| := by linarith
        calc |τ| ^ (2 * σ) ≤ ((1 + |τ|) / 3) ^ (2 * σ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) h3 h.le
          _ = (1 + |τ|) ^ (2 * σ) * (3 : ℝ) ^ (-(2 * σ)) := by
              rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]
              ring
          _ ≤ (1 + |τ|) ^ (2 * σ) * c2 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              have := neg_le_abs σlo
              linarith
          _ = _ := by ring
    calc _ ≤ C0 * |τ| ^ (2 * σ) := hq
      _ ≤ C0 * (c2 * (1 + |τ|) ^ (2 * σ)) := mul_le_mul_of_nonneg_left hpow hC0
      _ = C0 * c2 * (1 + |τ|) ^ (2 * σ) := by ring
      _ ≤ (C0 * c2 + max C1 0 / c0) * (1 + |τ|) ^ (2 * σ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ max C1 0 / c0 := by positivity
          linarith
  · replace hτ12 := not_le.mp hτ12
    have hmem : (σ, τ) ∈ Set.Icc σlo Λ ×ˢ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
      have := abs_lt.mp hτ12
      exact ⟨⟨hz1, hz2⟩, show -1 / 2 ≤ τ by linarith [this.1], show τ ≤ 1 / 2 by linarith [this.2]⟩
    have hb := hC1 (σ, τ) hmem
    have hzz : ((σ : ℂ) + (τ : ℂ) * Complex.I) = z := Complex.re_add_im z
    simp only [hzz] at hb
    rw [div_eq_mul_inv]
    have hlow : c0 ≤ (1 + |τ|) ^ (2 * σ) := by
      rcases le_or_gt 0 σ with h | h
      · calc c0 ≤ 1 := min_le_left _ _
          _ ≤ (1 + |τ|) ^ (2 * σ) := Real.one_le_rpow (by linarith [abs_nonneg τ]) (by linarith)
      · calc c0 ≤ (3 / 2 : ℝ) ^ (2 * σlo) := min_le_right _ _
          _ ≤ (3 / 2 : ℝ) ^ (2 * σ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ ≤ (1 + |τ|) ^ (2 * σ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hC1' : ‖Complex.Gamma (β + z) * (Complex.Gamma (β - z))⁻¹‖ ≤ max C1 0 :=
      hb.trans (le_max_left _ _)
    have : max C1 0 ≤ (max C1 0 / c0) * (1 + |τ|) ^ (2 * σ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0pos]
      exact mul_le_mul_of_nonneg_left hlow (le_max_right _ _)
    have hC0' : 0 ≤ C0 * c2 * (1 + |τ|) ^ (2 * σ) := by positivity
    nlinarith [hC1', this, hC0']

theorem rpow_shift_bound (e ρ t : ℝ) :
    (1 + |t + ρ|) ^ e ≤ (1 + |ρ|) ^ |e| * (1 + |t|) ^ e := by
  rcases le_or_gt 0 e with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ h
    have := abs_add_le t ρ
    nlinarith [abs_nonneg ρ, abs_nonneg t]
  · rw [abs_of_neg h]
    have h1 : (1 + |t|) / (1 + |ρ|) ≤ 1 + |t + ρ| := by
      rw [div_le_iff₀ (by positivity)]
      have : |t| ≤ |t + ρ| + |ρ| := by
        have := abs_sub (t + ρ) ρ
        simpa using this
      nlinarith [abs_nonneg ρ, abs_nonneg (t + ρ)]
    calc (1 + |t + ρ|) ^ e ≤ ((1 + |t|) / (1 + |ρ|)) ^ e :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 h.le
      _ = (1 + |ρ|) ^ (-e) * (1 + |t|) ^ e := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
          ring

end HeckeSkeleton.ThetaKernel
