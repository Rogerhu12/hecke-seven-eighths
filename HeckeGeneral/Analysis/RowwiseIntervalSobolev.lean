import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! An elementary rowwise Sobolev consumer. There are no arithmetic or
moment hypotheses: the derivative and its continuity are explicit, and the
right side is the actual integral of the row energies. Anchoring at the
left endpoint avoids selecting row-dependent mean-value points. -/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory Set
open scoped BigOperators Topology

theorem norm_sq_derivative_bound (z w : ℂ) :
    ‖2 * inner ℝ z w‖ ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  calc
    ‖2 * inner ℝ z w‖ = 2 * |inner ℝ z w| := by simp [norm_mul]
    _ ≤ 2 * (‖z‖ * ‖w‖) := mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm z w) (by norm_num)
    _ ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- A pointwise square is bounded by its anchored value and the actual
integral of the function and derivative squares on the entire interval. -/
theorem norm_sq_le_endpoint_add_integral
    (f f' : ℝ → ℂ) {a b x : ℝ} (hx : x ∈ Icc a b)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Icc a b)) :
    ‖f x‖ ^ 2 ≤ ‖f a‖ ^ 2 +
      ∫ t in a..b, (‖f t‖ ^ 2 + ‖f' t‖ ^ 2) := by
  let B : ℝ → ℝ := fun t => ‖f t‖ ^ 2 + ‖f' t‖ ^ 2
  have hfc : ContinuousOn f (Icc a b) := HasDerivAt.continuousOn hderiv
  have hBc : ContinuousOn B (Icc a b) := (hfc.norm.pow 2).add (hcont.norm.pow 2)
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hnorm : ‖‖f x‖ ^ 2 - ‖f a‖ ^ 2‖ ≤ ∫ t in a..x, B t := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le hx.1
      ((hfc.norm.pow 2).mono hsub)
    · intro t ht
      exact (hderiv t (hsub ⟨ht.1.le, ht.2.le⟩)).norm_sq.differentiableAt.differentiableWithinAt
    · exact Filter.Eventually.of_forall (fun t ht => by
        change ‖deriv (fun u => ‖f u‖ ^ 2) t‖ ≤ B t
        rw [(hderiv t (hsub ⟨ht.1.le, ht.2.le⟩)).norm_sq.deriv]
        exact norm_sq_derivative_bound (f t) (f' t))
    · exact (hBc.mono hsub).intervalIntegrable_of_Icc hx.1
  have hmono : (∫ t in a..x, B t) ≤ ∫ t in a..b, B t :=
    intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (hBc.intervalIntegrable_of_Icc (hx.1.trans hx.2))
  have hle := (Real.le_norm_self (‖f x‖ ^ 2 - ‖f a‖ ^ 2)).trans (hnorm.trans hmono)
  dsimp [B] at hle
  linarith

/-- Each row may select a different point. The finite sum is taken before
the energy integral, which is the essential order in the source argument. -/
theorem sum_norm_sq_le_endpoint_add_integral
    {ι : Type*} (F : Finset ι) (f f' : ι → ℝ → ℂ)
    {a b : ℝ} (hab : a ≤ b) (x : ι → ℝ) (hx : ∀ i ∈ F, x i ∈ Icc a b)
    (hderiv : ∀ i ∈ F, ∀ t ∈ Icc a b, HasDerivAt (f i) (f' i t) t)
    (hcont : ∀ i ∈ F, ContinuousOn (f' i) (Icc a b)) :
    (∑ i ∈ F, ‖f i (x i)‖ ^ 2) ≤ (∑ i ∈ F, ‖f i a‖ ^ 2) +
      ∫ t in a..b, ∑ i ∈ F, (‖f i t‖ ^ 2 + ‖f' i t‖ ^ 2) := by
  have hi (i : ι) (hI : i ∈ F) :
      IntervalIntegrable (fun t => ‖f i t‖ ^ 2 + ‖f' i t‖ ^ 2) volume a b :=
    (((HasDerivAt.continuousOn (hderiv i hI)).norm.pow 2).add
      ((hcont i hI).norm.pow 2)).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_finsetSum hi, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hI => norm_sq_le_endpoint_add_integral
    (f i) (f' i) (hx i hI) (hderiv i hI) (hcont i hI))

end HeckeGeneral.Analysis
