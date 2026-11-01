import ExpansionDetector.IdealDirichletProduct
import ExpansionDetector.IdealTerminal
import ExpansionDetector.ExponentialMellin
import ExpansionDetector.ExponentialSummability

/-! Exact Gamma smoothing of the explicit ideal Moebius detector. The only
L-function data are its ordinary initial Dirichlet series and absolute
convergence. The same coefficients, cutoff, and character weight occur in
the finite inverse and in the smoothed and terminal source. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open MeasureTheory Set
open scoped NumberField Classical BigOperators nonZeroDivisors
variable {K : Type*} [Field K] [NumberField K]

lemma countable_integralIdeals : Countable (Ideal (𝓞 K)) := by
  apply Set.countable_univ_iff.mp
  have heq : (Set.univ : Set (Ideal (𝓞 K))) =
      ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  rw [heq]
  exact Set.countable_iUnion (fun n => (Ideal.finite_setOfPred_absNorm_le n).countable)

abbrev NonzeroIntegralIdeal : Type _ := ↥((Ideal (𝓞 K))⁰)

def nonzeroIdealNorm (I : NonzeroIntegralIdeal (K := K)) : ℝ := Ideal.absNorm I.val

lemma nonzeroIdealNorm_pos (I : NonzeroIntegralIdeal (K := K)) : 0 < nonzeroIdealNorm I :=
  Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

lemma one_le_nonzeroIdealNorm (I : NonzeroIntegralIdeal (K := K)) : 1 ≤ nonzeroIdealNorm I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.succ_le_iff.mpr (Ideal.absNorm_pos_of_nonZeroDivisors I)

lemma support_subset_nonzero_of_zero {f : Ideal (𝓞 K) → ℂ} (h0 : f 0 = 0) :
    Function.support f ⊆ (Ideal (𝓞 K))⁰ := by
  intro I hI
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro heq
  subst I
  exact hI h0

lemma coefficient_initial_majorant_summable
    (w : Ideal (𝓞 K) →*₀ ℂ) (hw : ∀ I, ‖w I‖ ≤ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (D : ℝ) (s : ℂ)
    (hs : 1 / 2 ≤ s.re)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-3 / 2 : ℝ))) :
    Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      ‖coefficient V D I.val * w I.val‖ * nonzeroIdealNorm I ^ (-(s.re + 2))) := by
  apply Summable.of_nonneg_of_le (fun I =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (nonzeroIdealNorm_pos I).le _)) _ hzeta
  intro I
  have hN := nonzeroIdealNorm_pos I
  have hc : ‖coefficient V D I.val * w I.val‖ ≤ nonzeroIdealNorm I := by
    rw [norm_mul]
    exact (mul_le_mul (norm_coefficient_le_norm V D hV I.val) (hw I.val)
      (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  calc
    _ ≤ nonzeroIdealNorm I * nonzeroIdealNorm I ^ (-(s.re + 2)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
    _ = nonzeroIdealNorm I ^ (-(s.re + 1)) := by
      conv_lhs => lhs; rw [← Real.rpow_one (nonzeroIdealNorm I)]
      rw [← Real.rpow_add hN]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_nonzeroIdealNorm I) (by linarith)

/-- The actual finite inverse has exactly the desired exponentially
smoothed ideal convolution at every initial base point Re(rho)>=1/2.
No zero or spike is used in this identity. -/
theorem actualIdeal_gamma_mellin_identity
    (w : Ideal (𝓞 K) →*₀ ℂ) (hw : ∀ I, ‖w I‖ ≤ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (D Y : ℝ) (hD : 0 < D) (hY : 0 < Y)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ∑' I : Ideal (𝓞 K), idealDirichletWeight w s I)
    (habs : ∀ s : ℂ, 1 < s.re → Summable (fun I : Ideal (𝓞 K) => ‖idealDirichletWeight w s I‖))
    (ρ : ℂ) (hρ : 1 / 2 ≤ ρ.re)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-3 / 2 : ℝ))) :
    Summable (smoothedTerm w V D (fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / Y) : ℂ))) ∧
    ExpansionDetector.Analytic.gammaDetector L (actualInverse w V D) ρ Y =
      ∑' I : Ideal (𝓞 K),
        smoothedTerm w V D (fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I := by
  letI := countable_integralIdeals (K := K)
  let c : NonzeroIntegralIdeal (K := K) → ℂ := fun I => coefficient V D I.val * w I.val
  let N : NonzeroIntegralIdeal (K := K) → ℝ := nonzeroIdealNorm
  have hN : ∀ I, 0 < N I := nonzeroIdealNorm_pos
  have hsum : Summable (fun I => ‖c I‖ * N I ^ (-(ρ.re + 2))) :=
    coefficient_initial_majorant_summable w hw V hV D ρ hρ hzeta
  let P : ℂ → ℂ := fun s => L s * actualInverse w V D s
  have hline (t : ℝ) : P (ρ + ExpansionDetector.Analytic.vertical 2 t) =
      ∑' I, c I * (N I : ℂ) ^ (-(ρ + ExpansionDetector.Analytic.vertical 2 t)) := by
    let s := ρ + ExpansionDetector.Analytic.vertical 2 t
    have hs : 1 < s.re := by dsimp [s]; simp only [Complex.add_re, ExpansionDetector.Analytic.vertical_re]; linarith
    have hp := initial_product_identity w V D hD hV hVzero L s (hL s hs) (habs s hs)
    have hsup : Function.support (fun I : Ideal (𝓞 K) =>
        coefficient V D I * w I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆ (Ideal (𝓞 K))⁰ :=
      support_subset_nonzero_of_zero (by rw [map_zero, mul_zero, zero_mul])
    have hsub := tsum_subtype_eq_of_support_subset hsup
    let e : NonzeroIntegralIdeal (K := K) ≃
        {I : Ideal (𝓞 K) // I ∈ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K)))} :=
      { toFun := fun I => ⟨I.val, I.property⟩
        invFun := fun I => ⟨I.val, I.property⟩
        left_inv := fun I => Subtype.ext rfl
        right_inv := fun I => Subtype.ext rfl }
    have he := e.tsum_eq (fun I => coefficient V D I.val * w I.val *
      (Ideal.absNorm I.val : ℂ) ^ (-s))
    have hfinal := (hp.trans hsub.symm).trans he.symm
    simpa only [P, c, N, nonzeroIdealNorm, s, e, Equiv.coe_fn_mk,
      Complex.ofReal_natCast] using hfinal
  have hm := ExpansionDetector.Analytic.exponential_mellin_series c N hN P ρ Y hY hsum hline
  let f : Ideal (𝓞 K) → ℂ :=
    smoothedTerm w V D (fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / Y) : ℂ))
  have hsup : Function.support f ⊆ (Ideal (𝓞 K))⁰ := by
    apply support_subset_nonzero_of_zero
    simp only [f, smoothedTerm, map_zero, mul_zero, zero_mul]
  have heq (I : NonzeroIntegralIdeal (K := K)) :
      c I * (N I : ℂ) ^ (-ρ) * (Real.exp (-N I / Y) : ℂ) = f I.val := by
    simp only [c, N, nonzeroIdealNorm, f, smoothedTerm, Complex.ofReal_natCast]
    ring
  have hsmNZ := (ExpansionDetector.Analytic.exponential_smoothed_series_summable c N hN ρ Y hY hsum).congr heq
  have hsm : Summable f :=
    ((hasSum_subtype_iff_of_support_subset hsup).mp hsmNZ.hasSum).summable
  refine ⟨hsm, ?_⟩
  change ExpansionDetector.Analytic.gammaDetector L (actualInverse w V D) ρ Y = _ at hm
  rw [hm]
  calc
    _ = ∑' I : NonzeroIntegralIdeal (K := K), f I.val := tsum_congr heq
    _ = ∑' I : Ideal (𝓞 K), f I := tsum_subtype_eq_of_support_subset hsup

end ExpansionDetector.IdealCutoff
