import HeckeGeneral.Analysis.GaussianContour
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!+# Logarithmic Gaussian derivatives and explicit polynomial bounds

Every derivative on the logarithmic line is an actual polynomial times the
same Gaussian. The recursively constructed polynomial has degree at most the
derivative order, and its coefficient sum gives a concrete bound. Translation
by an annulus index is included in the derivative identity.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Polynomial
open scoped BigOperators

def realLogGaussian (u : ℝ) : ℝ := Real.exp (-(u ^ 2) / 4)

def gaussianDerivativePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (gaussianDerivativePolynomial n).derivative -
      C (1 / 2) * X * gaussianDerivativePolynomial n

theorem hasDerivAt_realLogGaussian (u : ℝ) :
    HasDerivAt realLogGaussian (-(u / 2) * realLogGaussian u) u := by
  have hd : HasDerivAt (fun x : ℝ => -(x ^ 2) / 4) (-(u / 2)) u := by
    convert! (((hasDerivAt_id u).pow 2).neg.div_const 4) using 1
    simp
    ring
  simpa only [realLogGaussian, mul_comm] using! hd.exp

theorem hasDerivAt_polynomial_gaussian (p : ℝ[X]) (u : ℝ) :
    HasDerivAt (fun x => p.eval x * realLogGaussian x)
      ((p.derivative - C (1 / 2) * X * p).eval u * realLogGaussian u) u := by
  convert! (p.hasDerivAt u).mul (hasDerivAt_realLogGaussian u) using 1
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

/-- The derivative formula holds for all orders, not only for finitely checked polynomials. -/
theorem iteratedDeriv_realLogGaussian (n : ℕ) (u : ℝ) :
    iteratedDeriv n realLogGaussian u = (gaussianDerivativePolynomial n).eval u * realLogGaussian u := by
  induction n generalizing u with
  | zero => simp [gaussianDerivativePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_polynomial_gaussian (gaussianDerivativePolynomial n) u).deriv

theorem iteratedDeriv_translated_realLogGaussian (n : ℕ) (k u : ℝ) :
    iteratedDeriv n (fun x => realLogGaussian (k + x)) u =
      (gaussianDerivativePolynomial n).eval (k + u) * realLogGaussian (k + u) := by
  rw [iteratedDeriv_comp_const_add]
  exact iteratedDeriv_realLogGaussian n (k + u)

/-- Differentiation raises the polynomial degree by at most one. -/
theorem natDegree_gaussianDerivativePolynomial_le (n : ℕ) :
    (gaussianDerivativePolynomial n).natDegree ≤ n := by
  induction n with
  | zero => simp [gaussianDerivativePolynomial]
  | succ n ih =>
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (ih.trans (Nat.le_succ n)))
    · apply natDegree_mul_le.trans
      have hlin : (C (1 / 2 : ℝ) * X).natDegree ≤ 1 := by
        apply natDegree_mul_le.trans
        simp
      omega

def polynomialAbsCoeffSum (p : ℝ[X]) : ℝ := ∑ i ∈ p.support, |p.coeff i|

theorem polynomialAbsCoeffSum_nonneg (p : ℝ[X]) : 0 ≤ polynomialAbsCoeffSum p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A coefficient-sum bound valid on the whole real line, with any degree upper bound. -/
theorem abs_polynomial_eval_le (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n) (u : ℝ) :
    |p.eval u| ≤ polynomialAbsCoeffSum p * (1 + |u|) ^ n := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, polynomialAbsCoeffSum, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hi' : i ≤ n := (le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hn
  calc
    |u| ^ i ≤ (1 + |u|) ^ i := by gcongr; linarith
    _ ≤ (1 + |u|) ^ n := pow_le_pow_right₀ (by linarith [abs_nonneg u]) hi'

def gaussianDerivativeBound (n : ℕ) : ℝ := polynomialAbsCoeffSum (gaussianDerivativePolynomial n)

theorem gaussianDerivativeBound_nonneg (n : ℕ) : 0 ≤ gaussianDerivativeBound n :=
  polynomialAbsCoeffSum_nonneg _

theorem abs_iteratedDeriv_realLogGaussian_le (n : ℕ) (u : ℝ) :
    |iteratedDeriv n realLogGaussian u| ≤
      gaussianDerivativeBound n * (1 + |u|) ^ n * Real.exp (-(u ^ 2) / 4) := by
  rw [iteratedDeriv_realLogGaussian, realLogGaussian, abs_mul,
    abs_of_pos (Real.exp_pos (-(u ^ 2) / 4))]
  exact mul_le_mul_of_nonneg_right
    (abs_polynomial_eval_le _ _ (natDegree_gaussianDerivativePolynomial_le n) u)
    (Real.exp_pos _).le

/-- Uniform bound throughout a fixed logarithmic annulus. -/
theorem abs_iteratedDeriv_gaussian_annulus_le (n : ℕ) (k C u : ℝ)
    (hC : 0 ≤ C) (hu : |u| ≤ C) :
    |iteratedDeriv n (fun x => realLogGaussian (k + x)) u| ≤
      gaussianDerivativeBound n * (1 + |k| + C) ^ n *
        Real.exp (-(max 0 (|k| - C)) ^ 2 / 4) := by
  rw [iteratedDeriv_translated_realLogGaussian]
  have hupper : |k + u| ≤ |k| + C := (abs_add_le k u).trans (add_le_add (le_refl _) hu)
  have hlower : max 0 (|k| - C) ≤ |k + u| := by
    apply max_le (abs_nonneg _)
    have h := abs_add_le (k + u) (-u)
    simp only [add_neg_cancel_right, abs_neg] at h
    linarith
  have hpoly := abs_polynomial_eval_le (gaussianDerivativePolynomial n) n
    (natDegree_gaussianDerivativePolynomial_le n) (k + u)
  rw [realLogGaussian, abs_mul, abs_of_pos (Real.exp_pos (-(k + u) ^ 2 / 4))]
  apply mul_le_mul
  · exact hpoly.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + |k + u| ≤ 1 + |k| + C) n)
      (gaussianDerivativeBound_nonneg n))
  · apply Real.exp_le_exp.mpr
    have hs := (sq_le_sq₀ (le_max_left 0 _) (abs_nonneg (k + u))).mpr hlower
    rw [sq_abs] at hs
    linarith
  · exact (Real.exp_pos _).le
  · exact mul_nonneg (gaussianDerivativeBound_nonneg n) (by positivity)

end HeckeGeneral.Analysis
