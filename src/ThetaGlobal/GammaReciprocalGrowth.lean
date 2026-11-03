module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Reciprocal Gamma has exponential growth on every vertical strip

Euler reflection and the convergent Gamma integral suffice here.  Shift a
fixed strip left by an integer, bound each recurrence denominator by the
imaginary part when its absolute value is at least one, and use compactness
for the remaining rectangle.  No Stirling estimate is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaReciprocalGrowth

open Complex MeasureTheory Set
open scoped Topology

theorem norm_Gamma_le_real {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have h₂ : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have h := (norm_sub_le (Complex.exp (-z * Complex.I))
    (Complex.exp (z * Complex.I))).trans (add_le_add h₁ h₂)
  norm_num only [norm_ofNat]
  linarith

theorem gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hz
  simpa only [hn, neg_im, natCast_im, neg_zero]

theorem inverse_reflection {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have hG := gamma_ne_zero_of_im_ne_zero hz
  have hG' : Complex.Gamma (1 - z) ≠ 0 :=
    gamma_ne_zero_of_im_ne_zero (by simpa using hz)
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hs : Complex.sin (Real.pi * z) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at h
    exact mul_ne_zero hG hG' h
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := (eq_div_iff hs).mp h
  apply (eq_div_iff hp).mpr
  apply mul_left_cancel₀ hG
  rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  simpa only [mul_assoc] using he.symm

/-- Moving right by an integer cannot increase the reciprocal Gamma norm
at heights whose absolute value is at least one. -/
theorem inverse_Gamma_add_nat_le (z : ℂ) (n : ℕ) (ht : 1 ≤ |z.im|) :
    ‖(Complex.Gamma (z + n))⁻¹‖ ≤ ‖(Complex.Gamma z)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (1 : ℝ) ≤ ‖z + (n : ℂ)‖ := by
      exact ht.trans (by simpa using Complex.abs_im_le_norm (z + (n : ℂ)))
    calc
      ‖(Complex.Gamma (z + (n + 1 : ℕ)))⁻¹‖ =
          ‖(Complex.Gamma (z + n + 1))⁻¹‖ := by
        rw [Nat.cast_add, Nat.cast_one, add_assoc]
      _ ≤ ‖z + (n : ℂ)‖ * ‖(Complex.Gamma (z + n + 1))⁻¹‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hn
      _ = ‖(Complex.Gamma (z + n))⁻¹‖ := by
        conv_rhs =>
          rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, norm_mul]
      _ ≤ _ := ih

theorem real_Gamma_bounded {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, Real.Gamma c ≤ C := by
  have hcont : ContinuousOn Real.Gamma (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun c hc => ha.trans_le hc.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro c hc
  exact (le_abs_self _).trans ((hC c hc).trans (le_max_left _ _))

/-- Uniform exponential growth on an arbitrary fixed vertical strip. -/
theorem inverse_Gamma_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, ∀ t : ℝ,
      ‖(Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  obtain ⟨M, hM, hMG⟩ := real_Gamma_bounded
    (a := 1 - b + n) (b := 1 - a + n) (by linarith)
  let rect : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 : ℝ) 1
  have hcompact : IsCompact rect := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun x : ℝ × ℝ =>
      (Complex.Gamma ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I))⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  let C := max (max B 0) (M / Real.pi)
  refine ⟨C, (le_max_right B 0).trans (le_max_left _ _), ?_⟩
  intro c hc t
  by_cases ht : 1 ≤ |t|
  · let z : ℂ := (c : ℂ) + (t : ℂ) * Complex.I - n
    have him : z.im = t := by simp [z]
    have himne : z.im ≠ 0 := by
      rw [him]
      intro hz
      have h : (1 : ℝ) ≤ 0 := by simpa only [hz, abs_zero] using ht
      exact (not_le_of_gt zero_lt_one) h
    have hre : 0 < (1 - z).re := by simp [z]; linarith [hc.2]
    have hreal : (1 - z).re ∈ Icc (1 - b + n) (1 - a + n) := by
      simp only [z, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, zero_sub, sub_zero, natCast_re, one_re]
      constructor <;> linarith [hc.1, hc.2]
    have hshift := inverse_Gamma_add_nat_le z n (by simpa [him] using ht)
    have hsin : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |t|) := by
      have h := norm_sin_le_exp (Real.pi * z)
      simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, him,
        abs_mul, abs_of_nonneg Real.pi_pos.le] using h
    have hbound : ‖(Complex.Gamma z)⁻¹‖ ≤
        (M / Real.pi) * Real.exp (Real.pi * |t|) := by
      rw [inverse_reflection himne, norm_div, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have hnum := mul_le_mul ((norm_Gamma_le_real hre).trans (hMG _ hreal)) hsin
        (norm_nonneg _) hM
      have hd := div_le_div_of_nonneg_right hnum Real.pi_pos.le
      convert hd using 1 <;> ring
    calc
      _ ≤ ‖(Complex.Gamma z)⁻¹‖ := by simpa [z] using hshift
      _ ≤ (M / Real.pi) * Real.exp (Real.pi * |t|) := hbound
      _ ≤ C * Real.exp (Real.pi * |t|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have htr : t ∈ Icc (-1 : ℝ) 1 := by
      have h := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨h.1.le, h.2.le⟩
    have hb := hB (c, t) ⟨hc, htr⟩
    have hC : B ≤ C := (le_max_left B 0).trans (le_max_left _ _)
    exact hb.trans (hC.trans (le_mul_of_one_le_right
      ((le_max_right B 0).trans (le_max_left _ _))
      (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg t)))))

end ThetaGlobal.GammaReciprocalGrowth

#print axioms ThetaGlobal.GammaReciprocalGrowth.inverse_Gamma_strip_bound
