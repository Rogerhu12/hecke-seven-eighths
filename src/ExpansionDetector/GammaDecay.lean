import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Elementary Gamma decay used by the zero detector. The two real-part bounds
are adapted from the supplied HeckeGammaQualitativeGrowth module (Apache 2.0).
The recurrence proof below supplies arbitrary inverse powers of height.
-/
noncomputable section
namespace ExpansionDetector.Analytic
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

lemma gamma_mul_im_pow_le (s : ℂ) (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ * |s.im| ^ n ≤ ‖Complex.Gamma (s + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖s + (n : ℂ)‖ := hs.trans (by
      simpa using Complex.abs_im_le_norm (s + (n : ℂ)))
    have hne : s + (n : ℂ) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ = (‖Complex.Gamma s‖ * |s.im| ^ n) * |s.im| := by rw [pow_succ]; ring
      _ ≤ ‖Complex.Gamma (s + n)‖ * |s.im| :=
        mul_le_mul_of_nonneg_right ih (abs_nonneg _)
      _ ≤ ‖Complex.Gamma (s + n)‖ * ‖s + n‖ :=
        mul_le_mul_of_nonneg_left (by simpa using Complex.abs_im_le_norm (s + (n : ℂ)))
          (norm_nonneg _)
      _ = ‖Complex.Gamma (s + (n + 1 : ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]
        ring

/-- Every fixed Gamma strip has decay of arbitrary polynomial order for
|t| >= 1. This uses only the Gamma integral and recurrence. -/
theorem detector_gamma_decay (a b : ℝ) (_hab : a ≤ b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (-(m : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (m : ℝ) (-a))
  have hn_m : (m : ℝ) < n := (le_max_left _ _).trans_lt hn
  have ha_n : 0 < a + n := by linarith [le_max_right (m : ℝ) (-a)]
  obtain ⟨C, hC, hbound⟩ := gamma_real_interval_bound (b := b + n) ha_n
  refine ⟨C, hC, ?_⟩
  intro σ hσ t ht
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hrec := gamma_mul_im_pow_le s (by simpa [hsim] using ht) n
  have hreal : 0 < (s + n).re := by simp only [Complex.add_re, hsre, Complex.natCast_re]; linarith [hσ.1]
  have htop : ‖Complex.Gamma (s + n)‖ ≤ C := by
    apply (gamma_norm_le_real hreal).trans
    apply hbound
    simp only [Complex.add_re, hsre, Complex.natCast_re, mem_Icc]
    constructor <;> linarith [hσ.1, hσ.2]
  have hlo : ‖Complex.Gamma s‖ ≤ C / |t| ^ n := by
    apply (le_div_iff₀ (pow_pos htpos n)).mpr
    simpa only [hsim] using hrec.trans htop
  calc
    ‖Complex.Gamma s‖ ≤ C / |t| ^ n := hlo
    _ = C * |t| ^ (-(n : ℝ)) := by rw [Real.rpow_neg htpos.le, Real.rpow_natCast, div_eq_mul_inv]
    _ ≤ C * |t| ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hC.le

end ExpansionDetector.Analytic
