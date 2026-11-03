import ExpansionDetector.ZeroDetectorBound
import Mathlib.Analysis.MellinInversion

/-! The exponential smoothing identity is proved from Mathlib Mellin inversion.
It is used term by term; the Gamma decay proof supplies absolute integrability. -/

noncomputable section
namespace ExpansionDetector.Analytic
open MeasureTheory Set
open scoped BigOperators Classical

lemma gamma_vertical_two_continuous :
    Continuous (fun t : ℝ => Complex.Gamma (vertical 2 t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
    (by dsimp [vertical]; fun_prop : ContinuousAt (fun t : ℝ => vertical 2 t) t)
  intro n hn
  have h := congrArg Complex.re hn
  simp only [vertical_re, Complex.neg_re, Complex.natCast_re] at h
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma gamma_vertical_two_norm_integrable :
    Integrable (fun t : ℝ => ‖Complex.Gamma (vertical 2 t)‖) := by
  obtain ⟨C, hC, h⟩ := detector_sz_gamma_moments 0 (by norm_num)
  simpa [vertical] using (h 2 (Or.inr (by simp)) 0).1

lemma exponential_mellin_eq {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) s = Complex.Gamma s := by
  rw [← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs]

/-- Exact 1/(2*pi) normalization of the standard exponential inverse Mellin transform. -/
theorem exponential_mellin_inversion (x : ℝ) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, Complex.Gamma (vertical 2 t) * (x : ℂ) ^ (-vertical 2 t)) =
        (Real.exp (-x) : ℂ) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hf : MellinConvergent f 2 := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (s := 2) (by norm_num))
  have hFm : Complex.VerticalIntegrable (mellin f) 2 := by
    have hi : Integrable (fun t : ℝ => Complex.Gamma (vertical 2 t)) :=
      (integrable_norm_iff gamma_vertical_two_continuous.aestronglyMeasurable).mp
        gamma_vertical_two_norm_integrable
    change Integrable (fun t : ℝ => mellin f (vertical 2 t))
    have heq : (fun t : ℝ => mellin f (vertical 2 t)) =
        (fun t : ℝ => Complex.Gamma (vertical 2 t)) := by
      funext t
      exact exponential_mellin_eq (by norm_num [vertical])
    rw [heq]
    exact hi
  have h := mellinInv_mellin_eq 2 f hx hf hFm (by dsimp [f]; fun_prop)
  have hm (t : ℝ) : mellin f (vertical 2 t) = Complex.Gamma (vertical 2 t) :=
    exponential_mellin_eq (by norm_num [vertical])
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, (x : ℂ) ^ (-vertical 2 t) * mellin f (vertical 2 t)) = f x at h
  simpa only [hm, mul_comm (Complex.Gamma _), f] using h

lemma exponential_mellin_integrable (x : ℝ) (hx : 0 < x) :
    Integrable (fun t : ℝ => Complex.Gamma (vertical 2 t) *
      (x : ℂ) ^ (-vertical 2 t)) := by
  have hc : Continuous (fun t : ℝ => Complex.Gamma (vertical 2 t) *
      (x : ℂ) ^ (-vertical 2 t)) := gamma_vertical_two_continuous.mul
    ((by dsimp [vertical]; fun_prop : Continuous (fun t : ℝ => -vertical 2 t)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
  apply (gamma_vertical_two_norm_integrable.mul_const (x ^ (-2 : ℝ))).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, vertical_re]

/-- Moving the actual ideal norm from the coefficient into the scalar
Mellin profile, with both signs fixed. -/
lemma mellin_weight_identity (q X : ℝ) (hq : 0 < q) (hX : 0 < X) (s z : ℂ) :
    (q : ℂ) ^ (-s) * ((q / X : ℝ) : ℂ) ^ (-z) =
      (X : ℂ) ^ z * (q : ℂ) ^ (-(s + z)) := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq.le hX.le,
    Complex.cpow_neg (X : ℂ), div_inv_eq_mul, neg_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne')]
  ring

theorem exponential_mellin_term (q X : ℝ) (hq : 0 < q) (hX : 0 < X) (s a : ℂ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, Complex.Gamma (vertical 2 t) *
        (a * (q : ℂ) ^ (-(s + vertical 2 t))) * (X : ℂ) ^ vertical 2 t) =
          a * (q : ℂ) ^ (-s) * (Real.exp (-q / X) : ℂ) := by
  have he (t : ℝ) : Complex.Gamma (vertical 2 t) *
      (a * (q : ℂ) ^ (-(s + vertical 2 t))) * (X : ℂ) ^ vertical 2 t =
        (a * (q : ℂ) ^ (-s)) *
          (Complex.Gamma (vertical 2 t) * ((q / X : ℝ) : ℂ) ^ (-vertical 2 t)) := by
    have h := mellin_weight_identity q X hq hX s (vertical 2 t)
    linear_combination -a * Complex.Gamma (vertical 2 t) * h
  simp_rw [he]
  rw [integral_const_mul]
  have h := exponential_mellin_inversion (q / X) (div_pos hq hX)
  rw [← neg_div] at h
  linear_combination (a * (q : ℂ) ^ (-s)) * h

lemma exponential_mellin_term_integrable (q X : ℝ) (hq : 0 < q) (hX : 0 < X)
    (s a : ℂ) :
    Integrable (fun t : ℝ => Complex.Gamma (vertical 2 t) *
      (a * (q : ℂ) ^ (-(s + vertical 2 t))) * (X : ℂ) ^ vertical 2 t) := by
  have hi := (exponential_mellin_integrable (q / X) (div_pos hq hX)).const_mul
    (a * (q : ℂ) ^ (-s))
  apply hi.congr
  filter_upwards [] with t
  have h := mellin_weight_identity q X hq hX s (vertical 2 t)
  linear_combination a * Complex.Gamma (vertical 2 t) * h

/-- Exact smoothing of a finite Dirichlet polynomial. Both sides are fully
specified by the same coefficient data. -/
theorem exponential_mellin_finite {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i) (s : ℂ) (X : ℝ) (hX : 0 < X) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, Complex.Gamma (vertical 2 t) *
        dirichletPolynomial S c N (s + vertical 2 t) * (X : ℂ) ^ vertical 2 t) =
      ∑ i ∈ S, c i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / X) : ℂ) := by
  simp only [dirichletPolynomial, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum S (fun i hi =>
    exponential_mellin_term_integrable (N i) X (hN i hi) hX s (c i)), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi =>
    exponential_mellin_term (N i) X (hN i hi) hX s (c i))

/-- Exact exponential smoothing of an absolutely convergent initial
Dirichlet line. The coefficient series may be infinite. -/
theorem exponential_mellin_series {ι : Type*} [Countable ι]
    (c : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (L : ℂ → ℂ) (s : ℂ) (X : ℝ) (hX : 0 < X)
    (hsum : Summable (fun i => ‖c i‖ * N i ^ (-(s.re + 2))))
    (hline : ∀ t : ℝ, L (s + vertical 2 t) =
      ∑' i, c i * (N i : ℂ) ^ (-(s + vertical 2 t))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, Complex.Gamma (vertical 2 t) * L (s + vertical 2 t) *
        (X : ℂ) ^ vertical 2 t) =
      ∑' i, c i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / X) : ℂ) := by
  let F : ι → ℝ → ℂ := fun i t => Complex.Gamma (vertical 2 t) *
    (c i * (N i : ℂ) ^ (-(s + vertical 2 t))) * (X : ℂ) ^ vertical 2 t
  have hi (i : ι) : Integrable (F i) :=
    exponential_mellin_term_integrable (N i) X (hN i) hX s (c i)
  have hnorm (i : ι) (t : ℝ) : ‖F i t‖ =
      (‖Complex.Gamma (vertical 2 t)‖ * X ^ (2 : ℝ)) *
        (‖c i‖ * N i ^ (-(s.re + 2))) := by
    dsimp [F]
    rw [norm_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [Complex.neg_re, Complex.add_re, vertical_re]
    ring
  have hnormint (i : ι) : (∫ t : ℝ, ‖F i t‖) =
      ((∫ t : ℝ, ‖Complex.Gamma (vertical 2 t)‖) * X ^ (2 : ℝ)) *
        (‖c i‖ * N i ^ (-(s.re + 2))) := by
    simp_rw [hnorm]
    rw [integral_mul_const, integral_mul_const]
  have hsumint : Summable (fun i => ∫ t : ℝ, ‖F i t‖) := by
    simp_rw [hnormint]
    exact hsum.mul_left _
  have heach (i : ι) : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F i t =
      c i * (N i : ℂ) ^ (-s) * (Real.exp (-N i / X) : ℂ) :=
    exponential_mellin_term (N i) X (hN i) hX s (c i)
  have hpoint (t : ℝ) : (∑' i, F i t) =
      Complex.Gamma (vertical 2 t) * L (s + vertical 2 t) *
        (X : ℂ) ^ vertical 2 t := by
    dsimp [F]
    rw [tsum_mul_right, tsum_mul_left, ← hline]
  rw [show (fun t : ℝ => Complex.Gamma (vertical 2 t) * L (s + vertical 2 t) *
      (X : ℂ) ^ vertical 2 t) = (fun t => ∑' i, F i t) by
        funext t; exact (hpoint t).symm,
    ← integral_tsum_of_summable_integral_norm hi hsumint, ← tsum_mul_left]
  exact tsum_congr heach

end ExpansionDetector.Analytic
