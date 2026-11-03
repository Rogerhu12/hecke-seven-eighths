import HeckeGeneral.Analysis.GaussianAnnularTail
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-!+# A fixed smooth cutoff in each Gaussian annulus

The Leibniz formula is applied to actual translated Gaussian profiles multiplied
by a fixed compactly supported smooth cutoff. Its derivatives have a summable
majorant uniformly over every point of the logarithmic line. Bounds for the
cutoff derivatives follow from smoothness and compact support.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open Function
open scoped BigOperators ContDiff

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_iteratedDeriv_subset f n)

/-- The cutoff constants exist for all orders as a consequence of compact support and smoothness. -/
theorem exists_compact_derivative_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n u, |iteratedDeriv n f u| ≤ B n := by
  have hb : ∀ n : ℕ, ∃ b : ℝ, ∀ u, |iteratedDeriv n f u| ≤ b := by
    intro n
    simpa only [Real.norm_eq_abs] using
      (hasCompactSupport_iteratedDeriv hc n).exists_bound_of_continuous
        (hf.continuous_iteratedDeriv n (by simp))
  choose B hB using hb
  refine ⟨fun n => max 0 (B n), fun _ => le_max_left _ _, fun n u => ?_⟩
  exact (hB n u).trans (le_max_right _ _)

def cutoffGaussianAnnulus (f : ℝ → ℝ) (k : ℤ) (u : ℝ) : ℝ :=
  realLogGaussian ((k : ℝ) + u) * f u

theorem contDiff_realLogGaussian : ContDiff ℝ ∞ realLogGaussian := by
  unfold realLogGaussian
  fun_prop

theorem cutoffGaussianAnnulus_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (k : ℤ) (u : ℝ) :
    iteratedDeriv n (cutoffGaussianAnnulus f k) u =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        iteratedDeriv j (fun x => realLogGaussian ((k : ℝ) + x)) u * iteratedDeriv (n - j) f u := by
  exact iteratedDeriv_fun_mul
    ((contDiff_realLogGaussian.comp (contDiff_const.add contDiff_id)).of_le (by simp)).contDiffAt
    (hf.of_le (by simp)).contDiffAt

def cutoffAnnulusMajorant (B : ℕ → ℝ) (n : ℕ) (C : ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * B (n - j) * gaussianAnnulusMajorant j C k

theorem cutoffAnnulusMajorant_nonneg (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (k : ℤ) : 0 ≤ cutoffAnnulusMajorant B n C k := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB _))
    (gaussianAnnulusMajorant_nonneg j C hC k)

theorem iteratedDeriv_cutoff_zero_outside {f : ℝ → ℝ} {C : ℝ}
    (hsupp : tsupport f ⊆ Set.Icc (-C) C) (n : ℕ) {u : ℝ} (hu : C < |u|) :
    iteratedDeriv n f u = 0 := by
  apply notMem_support.mp
  intro h
  have hm := hsupp ((tsupport_iteratedDeriv_subset f n) (subset_tsupport _ h))
  have hle : |u| ≤ C := abs_le.mpr hm
  exact (not_lt_of_ge hle) hu

/-- One explicit majorant works uniformly on and outside the cutoff support. -/
theorem abs_cutoffGaussianAnnulus_deriv_le (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hb : ∀ j u, |iteratedDeriv j f u| ≤ B j)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (hsupp : tsupport f ⊆ Set.Icc (-C) C)
    (k : ℤ) (u : ℝ) :
    |iteratedDeriv n (cutoffGaussianAnnulus f k) u| ≤ cutoffAnnulusMajorant B n C k := by
  rw [cutoffGaussianAnnulus_deriv f hf]
  unfold cutoffAnnulusMajorant
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hu : |u| ≤ C
  · rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ ((n.choose j : ℝ) * gaussianAnnulusMajorant j C k) * B (n - j) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (abs_iteratedDeriv_gaussian_annulus_le j k C u hC hu) (Nat.cast_nonneg _)
        · exact hb _ u
        · exact abs_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (gaussianAnnulusMajorant_nonneg j C hC k)
      _ = _ := by ring
  · rw [iteratedDeriv_cutoff_zero_outside hsupp (n - j) (lt_of_not_ge hu), mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB _))
      (gaussianAnnulusMajorant_nonneg j C hC k)

theorem summable_cutoffAnnulusMajorant (B : ℕ → ℝ) (n : ℕ) (C A : ℝ) (hC : 0 ≤ C) :
    Summable (fun k : ℤ => Real.exp (A * |(k : ℝ)|) * cutoffAnnulusMajorant B n C k) := by
  unfold cutoffAnnulusMajorant
  simp_rw [Finset.mul_sum]
  apply summable_sum
  intro j _
  have h := (summable_gaussianAnnulusMajorant j C A hC).mul_left ((n.choose j : ℝ) * B (n - j))
  convert! h using 1
  funext k
  ring

/-- Weighted annular derivative estimates now apply to the actual cut-off Gaussian profiles. -/
theorem summable_cutoffGaussianAnnulus_derivatives (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (n : ℕ) (C A : ℝ) (hC : 0 ≤ C)
    (hsupp : tsupport f ⊆ Set.Icc (-C) C) (u : ℤ → ℝ) :
    Summable (fun k : ℤ => Real.exp (A * |(k : ℝ)|) *
      |iteratedDeriv n (cutoffGaussianAnnulus f k) (u k)|) := by
  obtain ⟨B, hB, hb⟩ := exists_compact_derivative_bounds hf hc
  apply (summable_cutoffAnnulusMajorant B n C A hC).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    exact mul_le_mul_of_nonneg_left
      (abs_cutoffGaussianAnnulus_deriv_le f hf B hB hb n C hC hsupp k (u k)) (Real.exp_pos _).le

end HeckeGeneral.Analysis
