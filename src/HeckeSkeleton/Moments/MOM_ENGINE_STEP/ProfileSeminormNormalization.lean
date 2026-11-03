import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Homogeneity of the original finite profile seminorms

The normalization uses the literal Euler-derivative integrals in
`testSeminorm`.  Every derivative and the finite maximum scale by the
same positive scalar, including the case where an individual integral
is zero.  Consequently one positive envelope normalizes any previously
chosen finite collection of derivative orders, before a child is passed
to the induction.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open MeasureTheory Set
open HeckeGeneral.ThetaSkeleton.Global

theorem eulerDerivative_const_mul (f : ℝ → ℂ) (c : ℂ) :
    eulerDerivative (fun x => c * f x) = fun x => c * eulerDerivative f x := by
  funext x
  simp only [eulerDerivative, deriv_const_mul_field]
  ring

theorem eulerDerivativeOrder_const_mul (f : ℝ → ℂ) (c : ℂ) (j : ℕ) :
    eulerDerivativeOrder j (fun x => c * f x) =
      fun x => c * eulerDerivativeOrder j f x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [eulerDerivativeOrder, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, eulerDerivative_const_mul]

theorem testIntegral_const_mul (f : ℝ → ℂ) (c : ℂ) (j : ℕ) (A : ℝ) :
    testIntegral (fun x => c * f x) j A = ‖c‖ * testIntegral f j A := by
  unfold testIntegral
  simp only [eulerDerivativeOrder_const_mul, norm_mul]
  calc
    _ = ∫ y in Ioi (0 : ℝ),
        ‖c‖ * (‖eulerDerivativeOrder j f y‖ *
          (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring
    _ = _ := integral_const_mul _ _

theorem testSeminorm_nonneg (f : ℝ → ℂ) (J : ℕ) (A : ℝ) :
    0 ≤ testSeminorm f J A := by
  unfold testSeminorm
  exact (le_max_left 0 (testIntegral f 0 A)).trans
    (Finset.le_sup' (fun j => max 0 (testIntegral f j A))
      (Finset.mem_range.mpr (Nat.succ_pos J)))

theorem testIntegral_le_testSeminorm (f : ℝ → ℂ) (J j : ℕ) (A : ℝ)
    (hj : j ≤ J) : testIntegral f j A ≤ testSeminorm f J A := by
  unfold testSeminorm
  exact (le_max_right 0 (testIntegral f j A)).trans
    (Finset.le_sup' (fun k => max 0 (testIntegral f k A))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

/-- The finite maximum is homogeneous for exactly the same scalar as
the original test, without replacing the seminorm by a pointwise bound. -/
theorem testSeminorm_positive_scale (f : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (J : ℕ) (A : ℝ) :
    testSeminorm (fun x => (c : ℂ) * f x) J A = c * testSeminorm f J A := by
  have hI (j : ℕ) : testIntegral (fun x => (c : ℂ) * f x) j A =
      c * testIntegral f j A := by
    rw [testIntegral_const_mul, Complex.norm_of_nonneg hc.le]
  apply le_antisymm
  · unfold testSeminorm
    apply Finset.sup'_le
    intro j hj
    rw [hI]
    apply max_le
    · exact mul_nonneg hc.le (testSeminorm_nonneg f J A)
    · exact mul_le_mul_of_nonneg_left
        (testIntegral_le_testSeminorm f J j A
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hc.le
  · have hscaled := testSeminorm_nonneg (fun x => (c : ℂ) * f x) J A
    have hbound : testSeminorm f J A ≤
        testSeminorm (fun x => (c : ℂ) * f x) J A / c := by
      unfold testSeminorm
      apply Finset.sup'_le
      intro j hj
      apply max_le (div_nonneg hscaled hc.le)
      apply (le_div_iff₀ hc).mpr
      have hh := testIntegral_le_testSeminorm
        (fun x => (c : ℂ) * f x) J j A
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      rw [hI] at hh
      simpa only [mul_comm] using hh
    exact (mul_le_mul_of_nonneg_left hbound hc.le).trans_eq (by field_simp [hc.ne'])

/-- A bound on the unnormalized profile yields a unit-ball profile.
The envelope is strictly positive, so the actual support is unchanged. -/
theorem testSeminorm_normalized_le_one (f : ℝ → ℂ) (B : ℝ) (hB : 0 < B)
    (J : ℕ) (A : ℝ) (hbound : testSeminorm f J A ≤ B) :
    testSeminorm (fun x => ((B⁻¹ : ℝ) : ℂ) * f x) J A ≤ 1 := by
  rw [testSeminorm_positive_scale f B⁻¹ (inv_pos.mpr hB)]
  calc
    _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hB.le)
    _ = 1 := inv_mul_cancel₀ hB.ne'

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.testSeminorm_positive_scale
#print axioms HeckeSkeleton.Moments.EngineStep.testSeminorm_normalized_le_one
