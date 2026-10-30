import HeckeSkeleton.ThetaKernel.Core
import ThetaGlobal.VerticalContour
import ThetaGlobal.VerticalInverseBounds

/-!
# Gaussian regularization of the actual project reflection kernel

The existing multiplier bounds apply to the original annular test.
Multiplication by `exp(ε s²)` preserves every contour shift for `0≤ε≤1`.
The resulting kernels converge pointwise and have a common quadratic tail,
uniformly over the finite power-class family. This is exactly the input
needed to remove the regularizer in the reflected arithmetic series.

Project-facing module; its original-project dependencies are not replaced
by axioms or by stub definitions.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.RegularizedKernelProject

open NumberField IsDedekindDomain MeasureTheory Filter
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ThetaKernel
open scoped Topology BigOperators Classical

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
  (F : FiniteMellinData K S) (θ : HeckeCharacter K)

def spectral (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (σ t : ℝ) : ℂ :=
  let w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  mellin V.toFun (-w) * reflectionMultiplier K S F θ u κ w

theorem spectral_integrable (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {σ : ℝ} (hσ : -(1 / 3 : ℝ) < σ) :
    Integrable (spectral F θ u κ V σ) := by
  have h := fz_integrable hF θ u κ V 0 (y := 1) (by norm_num) hσ
  change Integrable (fun t : ℝ =>
    mellin V.toFun (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      reflectionMultiplier K S F θ u κ ((σ : ℂ) + (t : ℂ) * Complex.I))
  simpa only [fz, pow_zero, one_mul, Complex.ofReal_one,
    Complex.one_cpow, mul_one] using h

def regularizedKernel (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (ε σ y : ℝ) : ℂ :=
  VerticalInverseBounds.regularizedInverseLine (spectral F θ u κ V σ) ε σ y

theorem regularizedKernel_eq_fz (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : SmoothAnnularTest) (ε σ y : ℝ) :
    regularizedKernel F θ u κ V ε σ y =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ,
        fz F θ u κ V 0 y ((σ : ℂ) + (t : ℂ) * Complex.I) *
          GaussianRegularization.verticalGaussian ε σ t := by
  simp only [regularizedKernel, VerticalInverseBounds.regularizedInverseLine,
    VerticalInverseBounds.powerPhase, spectral, fz, pow_zero, one_mul]

set_option maxHeartbeats 1000000 in
theorem regularizedKernel_shift (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    {y a b : ℝ} (hy : 0 < y) (ha : -(1 / 3 : ℝ) < a) (hab : a ≤ b) :
    regularizedKernel F θ u κ V ε a y = regularizedKernel F θ u κ V ε b y := by
  obtain ⟨CM, hCM, hM⟩ := reflectionMultiplier_bound_pt hF θ u κ ha hab
  obtain ⟨J, hJ₀, hJ₁⟩ := exists_exponent K b 0
  obtain ⟨C, hC₀, hC⟩ := fz_strip_bound (F := F) θ u κ V hab hCM
    (fun s hs₀ hs₁ => hM s hs₀ hs₁) (h := 0) (J := J) (by omega) hy
  rw [regularizedKernel_eq_fz, regularizedKernel_eq_fz]
  congr 1
  exact VerticalContour.verticalIntegral_regularized_eq_of_poly_strip
    (f := fz F θ u κ V 0 y) hab
    (e := (J : ℝ) - 0 - 4 * ncx K * max b 0)
    (by linarith) hC₀ hε₀ hε₁
    (fun z hz₀ hz₁ => differentiableAt_fz hF θ u κ V 0 hy (by linarith))
    (by simpa only [Nat.cast_zero] using hC)

/-- Uniformity includes all actual local sixth-power classes and all
regularizers in `[0,1]`; the test is fixed before this constant is chosen. -/
theorem uniform_quadratic_tail [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) (u : SixthUnitClasses K S)
    (V : SmoothAnnularTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ κ y, 0 < y →
      ‖regularizedKernel F θ u κ V ε 0 y‖ ≤ C * y ^ (-2 : ℝ) := by
  letI := Fintype.ofFinite (SixthLocalClasses K S)
  have hspec (κ : SixthLocalClasses K S) : Integrable (spectral F θ u κ V 2) :=
    spectral_integrable F θ hF u κ V (by norm_num)
  choose C hC hc using fun κ =>
    VerticalInverseBounds.uniform_tail (spectral F θ u κ V 2) (hspec κ) 2
  refine ⟨∑ κ, C κ, Finset.sum_nonneg (fun κ _ => hC κ), ?_⟩
  intro ε hε₀ hε₁ κ y hy
  rw [regularizedKernel_shift F θ hF u κ V hε₀ hε₁ hy
    (a := 0) (b := 2) (by norm_num) (by norm_num)]
  exact (hc κ ε hε₀ hε₁ y hy).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun κ _ => hC κ) (Finset.mem_univ κ))
      (Real.rpow_nonneg hy.le _))

theorem regularizedKernel_tendsto (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (V : SmoothAnnularTest) (ε : ℕ → ℝ)
    (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n => regularizedKernel F θ u κ V (ε n) 0 y) atTop
      (𝓝 (mellinReflectionKernel K S F θ u κ V.toFun 0 y)) := by
  exact VerticalInverseBounds.regularizedInverseLine_tendsto
    (spectral F θ u κ V 0)
    (spectral_integrable F θ hF u κ V (by norm_num)) ε hε₀ hε₁ hε 0 hy

end ThetaGlobal.RegularizedKernelProject
