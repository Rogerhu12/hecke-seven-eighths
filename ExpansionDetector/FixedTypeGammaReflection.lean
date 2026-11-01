import ExpansionDetector.GammaDecay
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic.FieldSimp

/-! The actual reflected Gamma-C multiplier on the complete dynamic
interval, for arbitrary fixed radial and angular type. Beta comparison is
adapted from the supplied HeckeFixedTypeGammaBound (Apache 2.0 provenance
recorded there); the full interval and arbitrary type bound below are new.
All reciprocal Gamma zeros at the Gamma poles are retained. -/
noncomputable section
namespace ExpansionDetector.Analytic
open MeasureTheory Set
open scoped Classical ComplexConjugate

private theorem beta_real_integral_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in (0 : ℝ)..1, t ^ (x - 1) * (1 - t) ^ (y - 1)) =
      Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t : ℝ in (0 : ℝ)..1,
      ((t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ)) =
      Complex.betaIntegral (x : ℂ) (y : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2), Complex.ofReal_sub, Complex.ofReal_one]
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hx) (by simpa using hy)]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.ofReal_add, Complex.Gamma_ofReal]

private theorem beta_norm_le_real (s : ℂ) {d : ℝ} (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.betaIntegral s (d : ℂ)‖ ≤
      Real.Gamma s.re * Real.Gamma d / Real.Gamma (s.re + d) := by
  rw [← beta_real_integral_eq s.re d hs hd]
  unfold Complex.betaIntegral
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  have hp : 0 < 1 - t := sub_pos.mpr ht.2
  rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

/-- Beta comparison uniform in the imaginary part. -/
theorem gamma_real_shift_ratio_bound (s : ℂ) (d : ℝ)
    (hs : 0 < s.re) (hd : 0 < d) :
    ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + (d : ℂ))‖ ≤
      Real.Gamma s.re / Real.Gamma (s.re + d) := by
  have h := beta_norm_le_real s hs hd
  have hg : 0 < Real.Gamma d := Real.Gamma_pos_of_pos hd
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs (by simpa using hd),
    norm_div, norm_mul, Complex.Gamma_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hg] at h
  apply (mul_le_mul_iff_right₀ hg).mp
  convert h using 1 <;> ring


lemma gamma_real_inverse_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, (Real.Gamma x)⁻¹ ≤ C := by
  have hc : Continuous (fun x : ℝ => (Complex.Gamma (x : ℂ))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos (ha.trans_le hx.1)
  have h := hC x hx
  rw [Complex.Gamma_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos] at h
  exact h.trans (le_max_left _ _)

/-- A fixed arbitrary infinity type has one polynomial reflected Gamma-C
bound throughout the dynamic real interval. There is no finite-order
hypothesis. This is the extra input needed for general-background plain
witness reflection. -/
theorem gammaC_fixedType_reflected_dynamic_bound (a τ : ℝ) (ha : 0 ≤ a) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ,
      -(1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 →
      ‖Complex.Gammaℂ (1 - s - (τ : ℂ) * Complex.I + (a : ℂ)) *
        (Complex.Gammaℂ (s + (τ : ℂ) * Complex.I + (a : ℂ)))⁻¹‖ ≤
          G * (2 + |s.im|) ^ 2 := by
  obtain ⟨M, hM, hMb⟩ := gamma_real_interval_bound
    (a := a + 1 / 2) (b := a + 2) (by linarith)
  obtain ⟨A, hA, hAb⟩ := gamma_real_inverse_interval_bound
    (a := a + 1) (b := a + 3) (by linarith)
  let P : ℝ := 3 + a + |τ|
  have hP : 1 ≤ P := by dsimp [P]; linarith [abs_nonneg τ]
  refine ⟨(M * A) * P ^ 2, by positivity, ?_⟩
  intro s hs
  let w : ℂ := s + (τ : ℂ) * Complex.I + (a : ℂ)
  let z : ℂ := 1 - s - (τ : ℂ) * Complex.I + (a : ℂ)
  have hwre : w.re = s.re + a := by simp [w]
  have hwim : w.im = s.im + τ := by simp [w]
  have hzre : z.re = 1 - s.re + a := by simp [z]
  have hshift : z + ((1 + 2 * s.re : ℝ) : ℂ) = conj (w + 2) := by
    apply Complex.ext <;> simp [z, w] <;> ring
  have hb := gamma_real_shift_ratio_bound z (1 + 2 * s.re)
    (by rw [hzre]; linarith [hs.2]) (by linarith [hs.1])
  rw [hshift, Complex.Gamma_conj, Complex.norm_conj] at hb
  have hnum : Real.Gamma z.re ≤ M := by
    apply hMb
    rw [hzre]
    constructor <;> linarith [hs.1, hs.2]
  have hden : 0 < Real.Gamma (z.re + (1 + 2 * s.re)) := by
    apply Real.Gamma_pos_of_pos
    rw [hzre]
    linarith [hs.1]
  have hinv : (Real.Gamma (z.re + (1 + 2 * s.re)))⁻¹ ≤ A := by
    apply hAb
    rw [hzre]
    constructor <;> linarith [hs.1, hs.2]
  have hmain : ‖Complex.Gamma z‖ / ‖Complex.Gamma (w + 2)‖ ≤ M * A := by
    apply hb.trans
    rw [div_eq_mul_inv]
    exact mul_le_mul hnum hinv (inv_nonneg.mpr hden.le) hM.le
  have hwbound : ‖w‖ ≤ P + |s.im| := by
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ (a + 1 / 2) + (|s.im| + |τ|) := by
        rw [hwre, hwim]
        exact add_le_add (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
          (abs_add_le _ _)
      _ ≤ P + |s.im| := by dsimp [P]; linarith
  have hfactor : P + |s.im| + 1 ≤ P * (2 + |s.im|) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (abs_nonneg s.im)]
  have hwpoly : ‖w‖ ≤ P * (2 + |s.im|) := by linarith
  have hw1poly : ‖w + 1‖ ≤ P * (2 + |s.im|) := by
    have hh := norm_add_le w (1 : ℂ)
    rw [norm_one] at hh
    linarith
  have hpoly : ‖w‖ * ‖w + 1‖ ≤ P ^ 2 * (2 + |s.im|) ^ 2 := by
    have hh := mul_le_mul hwpoly hw1poly (norm_nonneg _) (by positivity)
    convert hh using 1 <;> ring
  have hrec : (Complex.Gamma w)⁻¹ = w * (w + 1) * (Complex.Gamma (w + 2))⁻¹ := by
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (w + 1)]
    ring_nf
  have hcore : ‖Complex.Gamma z * (Complex.Gamma w)⁻¹‖ ≤
      (M * A) * (P ^ 2 * (2 + |s.im|) ^ 2) := by
    rw [hrec, norm_mul, norm_mul, norm_mul, norm_inv]
    calc
      _ = (‖Complex.Gamma z‖ / ‖Complex.Gamma (w + 2)‖) * (‖w‖ * ‖w + 1‖) := by ring
      _ ≤ _ := mul_le_mul hmain hpoly (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_pos hM hA).le
  have hbase : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖Complex.Gammaℂ z * (Complex.Gammaℂ w)⁻¹‖ =
      ((2 * Real.pi) ^ (-z.re) / (2 * Real.pi) ^ (-w.re)) *
        ‖Complex.Gamma z * (Complex.Gamma w)⁻¹‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv]
    have h1 : ‖(2 * (Real.pi : ℂ)) ^ (-z)‖ = (2 * Real.pi) ^ (-z.re) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase, Complex.neg_re]
    have h2 : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ = (2 * Real.pi) ^ (-w.re) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase, Complex.neg_re]
    rw [h1, h2]
    norm_num
    ring
  have hscale : (2 * Real.pi) ^ (-z.re) / (2 * Real.pi) ^ (-w.re) ≤ 1 := by
    rw [← Real.rpow_sub hbase]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi])
    rw [hzre, hwre]
    linarith [hs.2]
  change ‖Complex.Gammaℂ z * (Complex.Gammaℂ w)⁻¹‖ ≤ _
  rw [hnorm]
  exact (mul_le_mul hscale hcore (norm_nonneg _) (by positivity)).trans_eq (by ring)

end ExpansionDetector.Analytic
