/-
Qualitative reciprocal Gamma bounds on an arbitrary vertical strip.

Adapted from Axiom DedekindZetaZeroFree snapshot
09afbb4ce6570c1615d58509dc197fc9f0956b7d:
Analysis/Gamma/ElementaryNormBounds.lean and
LFunctions/Hecke/ReciprocalGammaFactorStripBounds.lean.
The elementary bounds in turn adapt openai/math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/NumberTheory/CubicMoment/Estimates/GammaElementaryGrowth.lean.
Upstream supplied no additional copyright/authorship header or NOTICE.
License: Apache-2.0; full license in sources/openai-math-LICENSE.txt.
Changes: merged the generic proofs, changed namespace/module syntax and
imports, and added real-place and arbitrary fixed-complex-shift corollaries.

At high height reflection moves Gamma to a positive-real-part strip, where
its norm is bounded by real Gamma. The remaining rectangle is compact and
reciprocal Gamma is entire, including its zero values at Gamma poles.
The constants may depend on the strip and the fixed shifts.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
namespace HeckeSkeleton.HeckeGammaQualitativeGrowth

noncomputable section
open MeasureTheory Set

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma gamma_norm_le_add_nat {s : ℂ} (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have him : (s+(n:ℂ)).im = s.im := by simp
    have hn : 1 ≤ ‖s+(n:ℂ)‖ := hs.trans (by simpa using Complex.abs_im_le_norm (s+(n:ℂ)))
    have hne : s+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (s+n)‖ := ih
      _ ≤ ‖s+(n:ℂ)‖*‖Complex.Gamma (s+n)‖ :=
        le_mul_of_one_le_left (_root_.norm_nonneg _) hn
      _ = ‖Complex.Gamma (s+(n+1:ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

lemma complex_sin_norm_le_exp_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hp : ‖Complex.exp (-s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self s.im
  have hm : ‖Complex.exp (s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs s.im
  have hd := (norm_sub_le (Complex.exp (-s*Complex.I)) (Complex.exp (s*Complex.I))).trans
    (add_le_add hp hm)
  norm_num
  simp only [neg_mul] at hd
  linarith

lemma gamma_real_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc a b, Real.Gamma x ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma (x:ℂ) ?_).comp Complex.continuous_ofReal.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    linarith [hx.1]
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (Complex.re_le_norm (Complex.Gamma (x:ℂ))).trans ((hM x hx).trans (le_max_left _ _))

end

end HeckeSkeleton.HeckeGammaQualitativeGrowth




namespace HeckeSkeleton.HeckeGammaQualitativeGrowth

private lemma gamma_inv_reflection {s : ℂ} (hs : s.im ≠ 0) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
  have hGam : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (fun m hm => hs (by rw [hm]; simp))
  have hGam1 : Complex.Gamma (1 - s) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have : (1 - s).im = 0 := by rw [hm]; simp
    simp [Complex.sub_im] at this
    exact hs this
  have h := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact mul_ne_zero hGam hGam1 h
  have h2 : Complex.Gamma (1 - s) =
      (Complex.Gamma s)⁻¹ * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) := by
    have := congrArg (fun x => (Complex.Gamma s)⁻¹ * x) h
    rw [← mul_assoc, inv_mul_cancel₀ hGam, one_mul] at this
    exact this
  rw [h2]
  field_simp

theorem gamma_inverse_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by

  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ≤ (n : ℝ) := ⟨Nat.ceil b, Nat.le_ceil b⟩

  obtain ⟨M, hMpos, hM⟩ :=
    gamma_real_interval_bound (a := 1 - b + n) (b := 1 - a + n) (by linarith)

  have hcont : Continuous fun p : ℝ × ℝ =>
      ‖(Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))⁻¹‖ := by
    apply Continuous.norm
    exact Complex.differentiable_one_div_Gamma.continuous.comp (by continuity)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
      |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max (M / Real.pi) (max C 1), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    rcases le_or_gt (1 : ℝ) |s.im| with hbig | hsmall
    ·
      have him : s.im ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hbig; norm_num at hbig
      have him1 : 1 ≤ |(1 - s).im| := by
        have : (1 - s).im = -s.im := by simp
        rw [this, abs_neg]; exact hbig
      have hre : (1 - s + (n : ℂ)).re = 1 - s.re + (n : ℝ) := by simp
      have hpos : 0 < (1 - s + (n : ℂ)).re := by
        rw [hre]; linarith
      have hmem : (1 - s + (n : ℂ)).re ∈ Set.Icc (1 - b + n) (1 - a + n) := by
        rw [hre, Set.mem_Icc]; constructor <;> linarith
      have hGbound : ‖Complex.Gamma (1 - s)‖ ≤ M := by
        calc ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma (1 - s + (n : ℂ))‖ :=
              gamma_norm_le_add_nat him1 n
          _ ≤ Real.Gamma ((1 - s + (n : ℂ)).re) := gamma_norm_le_real hpos
          _ ≤ M := hM _ hmem
      have hSbound : ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
        have h := complex_sin_norm_le_exp_im ((Real.pi : ℂ) * s)
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          abs_mul, abs_of_pos Real.pi_pos] at h
        exact h
      rw [gamma_inv_reflection him, norm_div, norm_mul]
      have hnorm : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
      rw [hnorm]
      calc ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin ((Real.pi : ℂ) * s)‖ / Real.pi
          ≤ M * Real.exp (Real.pi * |s.im|) / Real.pi := by
            apply div_le_div_of_nonneg_right _ Real.pi_pos.le
            exact mul_le_mul hGbound hSbound (norm_nonneg _) hMpos.le
        _ = M / Real.pi * Real.exp (Real.pi * |s.im|) := by ring
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    ·
      have hGpos : 0 < max (M / Real.pi) (max C 1) :=
        lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _))
      have hmemK : (s.re, s.im) ∈ Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1 :=
        ⟨⟨hsa, hsb⟩,
          ⟨by linarith [neg_abs_le s.im, hsmall], by linarith [le_abs_self s.im, hsmall]⟩⟩
      have hCapp := hC (s.re, s.im) hmemK
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Complex.re_add_im] at hCapp
      calc ‖(Complex.Gamma s)⁻¹‖ ≤ C := hCapp
        _ ≤ max (M / Real.pi) (max C 1) := le_trans (le_max_left C 1) (le_max_right _ _)
        _ = max (M / Real.pi) (max C 1) * 1 := (mul_one _).symm
        _ ≤ max (M / Real.pi) (max C 1) * Real.exp (Real.pi * |s.im|) :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) hGpos.le

theorem gammaC_inverse_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ GC : ℝ, 0 < GC ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℂ s)⁻¹‖ ≤ GC * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gamma_inverse_strip_exp_bound a b hab
  refine ⟨max (G * (2 * Real.pi) ^ b / 2) 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro s hs
    obtain ⟨hsa, hsb⟩ := hs
    have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring

    have hpow : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ = (2 * Real.pi) ^ s.re / 2 := by
      rw [norm_inv, norm_mul, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re, Complex.norm_ofNat, Real.rpow_neg (by positivity)]
      field_simp
    have hle : (2 * Real.pi) ^ s.re ≤ (2 * Real.pi) ^ b :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hsb
    have hGs : ‖(Complex.Gamma s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := hG s ⟨hsa, hsb⟩
    rw [Complex.Gammaℂ_def]
    have hnorm : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s)⁻¹‖ =
        ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖ := by
      rw [mul_inv, norm_mul]
    rw [hnorm]
    calc ‖(2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖
        ≤ ((2 * Real.pi) ^ s.re / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          refine mul_le_mul hpow.le hGs (norm_nonneg _) ?_
          positivity
      _ ≤ ((2 * Real.pi) ^ b / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hGpos.le (Real.exp_pos _).le)
          exact div_le_div_of_nonneg_right hle (by norm_num)
      _ = G * (2 * Real.pi) ^ b / 2 * Real.exp (Real.pi * |s.im|) := by ring
      _ ≤ max (G * (2 * Real.pi) ^ b / 2) 1 * Real.exp (Real.pi * |s.im|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end HeckeSkeleton.HeckeGammaQualitativeGrowth


namespace HeckeSkeleton.HeckeGammaQualitativeGrowth

/-- The real-place factor has the same convenient exponential upper bound.
This is qualitative; no Stirling asymptotic or finite-order character is used. -/
theorem gammaR_inverse_strip_exp_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ GR : ℝ, 0 < GR ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ GR * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gamma_inverse_strip_exp_bound (a / 2) (b / 2)
    (by linarith)
  refine ⟨Real.pi ^ (b / 2) * G, by positivity, ?_⟩
  intro s hs
  have hGs : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤
      G * Real.exp (Real.pi * |s.im| / 2) := by
    have hmem : a / 2 ≤ (s / 2).re ∧ (s / 2).re ≤ b / 2 := by
      simp only [Complex.div_ofNat_re]
      constructor <;> linarith [hs.1, hs.2]
    have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
    calc
      ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ G * Real.exp (Real.pi * |(s / 2).im|) :=
        hG (s / 2) hmem
      _ = G * Real.exp (Real.pi * |s.im| / 2) := by rw [him, mul_div_assoc]
  have hp : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ = Real.pi ^ (s.re / 2) := by
    rw [← Complex.cpow_neg, neg_div, neg_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.div_ofNat_re]
  have hpow : Real.pi ^ (s.re / 2) ≤ Real.pi ^ (b / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (by linarith [hs.2])
  have he : Real.exp (Real.pi * |s.im| / 2) ≤ Real.exp (Real.pi * |s.im|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, abs_nonneg s.im]
  rw [Complex.Gammaℝ_def, mul_inv, norm_mul, hp]
  calc
    Real.pi ^ (s.re / 2) * ‖(Complex.Gamma (s / 2))⁻¹‖ ≤
        Real.pi ^ (b / 2) * (G * Real.exp (Real.pi * |s.im| / 2)) :=
      mul_le_mul hpow hGs (norm_nonneg _) (by positivity)
    _ ≤ Real.pi ^ (b / 2) * (G * Real.exp (Real.pi * |s.im|)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hGpos.le)
        (by positivity)
    _ = (Real.pi ^ (b / 2) * G) * Real.exp (Real.pi * |s.im|) := by ring

/-- A fixed arbitrary complex shift only changes the qualitative constant. -/
theorem gammaC_inverse_shifted_strip_exp_bound (a b : ℝ) (hab : a ≤ b) (c : ℂ) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℂ (s + c))⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gammaC_inverse_strip_exp_bound (a + c.re) (b + c.re)
    (by linarith)
  refine ⟨G * Real.exp (Real.pi * |c.im|), by positivity, ?_⟩
  intro s hs
  have hsc := hG (s + c) ⟨by simpa using add_le_add_right hs.1 c.re,
    by simpa using add_le_add_right hs.2 c.re⟩
  have he : Real.exp (Real.pi * |(s + c).im|) ≤
      Real.exp (Real.pi * |c.im|) * Real.exp (Real.pi * |s.im|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := abs_add_le s.im c.im
    simp only [Complex.add_im]
    nlinarith [Real.pi_pos]
  calc
    ‖(Complex.Gammaℂ (s + c))⁻¹‖ ≤ G * Real.exp (Real.pi * |(s + c).im|) := hsc
    _ ≤ G * (Real.exp (Real.pi * |c.im|) * Real.exp (Real.pi * |s.im|)) :=
      mul_le_mul_of_nonneg_left he hGpos.le
    _ = (G * Real.exp (Real.pi * |c.im|)) * Real.exp (Real.pi * |s.im|) := by ring

theorem gammaR_inverse_shifted_strip_exp_bound (a b : ℝ) (hab : a ≤ b) (c : ℂ) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(Complex.Gammaℝ (s + c))⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨G, hGpos, hG⟩ := gammaR_inverse_strip_exp_bound (a + c.re) (b + c.re)
    (by linarith)
  refine ⟨G * Real.exp (Real.pi * |c.im|), by positivity, ?_⟩
  intro s hs
  have hsc := hG (s + c) ⟨by simpa using add_le_add_right hs.1 c.re,
    by simpa using add_le_add_right hs.2 c.re⟩
  have he : Real.exp (Real.pi * |(s + c).im|) ≤
      Real.exp (Real.pi * |c.im|) * Real.exp (Real.pi * |s.im|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht := abs_add_le s.im c.im
    simp only [Complex.add_im]
    nlinarith [Real.pi_pos]
  calc
    ‖(Complex.Gammaℝ (s + c))⁻¹‖ ≤ G * Real.exp (Real.pi * |(s + c).im|) := hsc
    _ ≤ G * (Real.exp (Real.pi * |c.im|) * Real.exp (Real.pi * |s.im|)) :=
      mul_le_mul_of_nonneg_left he hGpos.le
    _ = (G * Real.exp (Real.pi * |c.im|)) * Real.exp (Real.pi * |s.im|) := by ring

end HeckeSkeleton.HeckeGammaQualitativeGrowth
