import HeckeSkeleton.ThetaKernel.Core
import ThetaGlobal.TestMellinLimit
import ThetaGlobal.VerticalContour
import ThetaGlobal.ScalarGaussianLimits

/-!
# The actual annular test: vertical integrability, uniform tails and limits

All assumptions of scalar Gaussian inversion are discharged for the
project's `SmoothAnnularTest`.  The contour estimate is applied to the
original test's entire Mellin transform.  The regularized test need not
be compactly supported, and no theorem requiring compact support is
applied to it.

This adapter depends on the original project and is listed separately
from the Mathlib-only verification bundle.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.RegularizedTestProject

open MeasureTheory Set Filter
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Topology

variable (V : SmoothAnnularTest)

theorem mellin_differentiable : Differentiable ℂ (mellin V.toFun) := by
  have h := (differentiable_mellin_neg V).comp differentiable_neg
  simpa only [Function.comp_def, neg_neg] using h

theorem spectral_line_bound (σ t : ℝ) :
    ‖mellin V.toFun ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (4 * (Iint V 0 (-σ) + Iint V 2 (-σ))) * (1 + |t|) ^ (-2 : ℝ) := by
  let w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have he : ((-σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = -w := by
    dsimp [w]
    push_cast
    ring
  have hb := pow_mul_norm_mellin_le V 2 (-σ) (-t)
  rw [he, norm_neg, neg_neg] at hb
  have ht : |t| ≤ ‖w‖ := by
    have h := Complex.abs_im_le_norm w
    simpa only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero,
      add_zero, zero_add] using h
  have hp : (1 + |t|) ^ 2 * ‖mellin V.toFun w‖ ≤
      4 * (Iint V 0 (-σ) + Iint V 2 (-σ)) := by
    calc
      _ ≤ (1 + ‖w‖) ^ 2 * ‖mellin V.toFun w‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) 2) (norm_nonneg _)
      _ ≤ _ := by norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hb; exact hb
  have hd : 0 < (1 + |t|) ^ 2 := by positivity
  have hq : ‖mellin V.toFun w‖ ≤
      (4 * (Iint V 0 (-σ) + Iint V 2 (-σ))) / (1 + |t|) ^ 2 :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hp)
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |t|) 2, Real.rpow_two]
  simpa only [div_eq_mul_inv] using hq

theorem vertical_integrable (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V.toFun) σ := by
  have hc : Continuous (fun t : ℝ =>
      mellin V.toFun ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    (mellin_differentiable V).continuous.comp (by fun_prop)
  exact ((VerticalContour.integrable_one_add_abs_rpow_neg
    (e := 2) (by norm_num)).const_mul _).mono' hc.aestronglyMeasurable
      (Eventually.of_forall (spectral_line_bound V σ))

theorem integrand_strip_bound {a b y : ℝ} (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖mellin V.toFun ((σ : ℂ) + (t : ℂ) * Complex.I) *
        VerticalInverseBounds.powerPhase σ y t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ) := by
  let B := 4 * (Iint V 0 (-b) + Iint V 0 (-a) +
    (Iint V 2 (-b) + Iint V 2 (-a)))
  have hB : 0 ≤ B := by
    dsimp [B]
    have := Iint_nonneg V 0 (-b)
    have := Iint_nonneg V 0 (-a)
    have := Iint_nonneg V 2 (-b)
    have := Iint_nonneg V 2 (-a)
    positivity
  refine ⟨B * (y ^ (-a) + y ^ (-b)), by positivity, ?_⟩
  intro σ hσ t
  have hi0 := Iint_strip_le V 0 (neg_le_neg hσ.2) (neg_le_neg hσ.1)
  have hi2 := Iint_strip_le V 2 (neg_le_neg hσ.2) (neg_le_neg hσ.1)
  have hc : 4 * (Iint V 0 (-σ) + Iint V 2 (-σ)) ≤ B := by
    dsimp [B]
    linarith
  have hm := (spectral_line_bound V σ t).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))
  have hp := rpow_neg_strip_le hy hσ.1 hσ.2
  rw [norm_mul, VerticalInverseBounds.powerPhase_norm σ t hy]
  calc
    _ ≤ (B * (1 + |t|) ^ (-2 : ℝ)) * (y ^ (-a) + y ^ (-b)) :=
      mul_le_mul hm hp (by positivity) (by positivity)
    _ = _ := by ring

def regularizedTest (ε σ y : ℝ) : ℂ :=
  VerticalInverseBounds.regularizedInverseLine
    (fun t => mellin V.toFun ((σ : ℂ) + (t : ℂ) * Complex.I)) ε σ y

theorem regularizedTest_shift {a b ε y : ℝ} (hab : a ≤ b)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hy : 0 < y) :
    regularizedTest V ε a y = regularizedTest V ε b y := by
  obtain ⟨C, hC, hb⟩ := integrand_strip_bound V (a := a) (b := b) hy
  unfold regularizedTest VerticalInverseBounds.regularizedInverseLine
  congr 1
  apply VerticalContour.verticalIntegral_regularized_eq_of_poly_strip
    (f := fun z => mellin V.toFun z * (y : ℂ) ^ (-z))
    hab (e := 2) (by norm_num) hC hε₀ hε₁
  · intro z _ _
    exact (mellin_differentiable V z).mul
      (DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne')))
  · exact hb

/-- A common quadratic tail for all smoothing parameters in `[0,1]`. -/
theorem uniform_quadratic_tail :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ y, 0 < y →
      ‖regularizedTest V ε 0 y‖ ≤ C * y ^ (-2 : ℝ) := by
  obtain ⟨C, hC, hc⟩ := VerticalInverseBounds.uniform_tail
    (fun t => mellin V.toFun ((2 : ℂ) + (t : ℂ) * Complex.I))
    (vertical_integrable V 2) 2
  refine ⟨C, hC, ?_⟩
  intro ε hε₀ hε₁ y hy
  rw [regularizedTest_shift V (a := 0) (b := 2) (by norm_num) hε₀ hε₁ hy]
  exact hc ε hε₀ hε₁ y hy

theorem pointwise_tendsto (ε : ℕ → ℝ)
    (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n => regularizedTest V (ε n) 0 y) atTop (𝓝 (V.toFun y)) := by
  have h := VerticalInverseBounds.regularizedInverseLine_tendsto
    (fun t => mellin V.toFun ((0 : ℂ) + (t : ℂ) * Complex.I))
    (vertical_integrable V 0) ε hε₀ hε₁ hε 0 hy
  have hinv := TestMellinLimit.inverseLine_mellin_eq V.toFun 0
    ((good_toFun V).integrableOn_mellin 0) (vertical_integrable V 0)
      hy V.smooth.continuous.continuousAt
  simp only [Complex.ofReal_zero, zero_add] at h hinv
  rw [hinv] at h
  simpa only [regularizedTest, Complex.ofReal_zero, zero_add] using h

end ThetaGlobal.RegularizedTestProject
