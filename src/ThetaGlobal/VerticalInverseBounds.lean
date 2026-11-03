import ThetaGlobal.GaussianRegularization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Uniform bounds and removal of the regularizer on a Mellin line

The spectral function below is the ORIGINAL annular-test Mellin transform
times its local multiplier. The estimate never invokes an annular-test
theorem on a Gaussian-smoothed, noncompactly supported test.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.VerticalInverseBounds

open MeasureTheory Filter
open scoped Topology

def powerPhase (σ y t : ℝ) : ℂ :=
  (y : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))

theorem powerPhase_norm (σ t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖powerPhase σ y t‖ = y ^ (-σ) := by
  rw [powerPhase, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem powerPhase_continuous (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous (powerPhase σ y) := by
  have h : Continuous (fun t : ℝ => -((σ : ℂ) + (t : ℂ) * Complex.I)) := by fun_prop
  apply h.const_cpow
  exact Or.inl (by exact_mod_cast hy.ne')

theorem integrable_line (F : ℝ → ℂ) (hF : Integrable F) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    Integrable (fun t => F t * powerPhase σ y t) := by
  apply Integrable.mono' (hF.norm.mul_const (y ^ (-σ)))
    (hF.aestronglyMeasurable.mul (powerPhase_continuous σ hy).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖F t * powerPhase σ y t‖ ≤ ‖F t‖ * y ^ (-σ)
  rw [norm_mul, powerPhase_norm σ t hy]

def inverseLine (F : ℝ → ℂ) (σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t, F t * powerPhase σ y t

def regularizedInverseLine (F : ℝ → ℂ) (ε σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t, (F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t

theorem regularized_line_integrable (F : ℝ → ℂ) (hF : Integrable F)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    Integrable (fun t => (F t * powerPhase σ y t) *
      GaussianRegularization.verticalGaussian ε σ t) :=
  GaussianRegularization.regularized_integrable _ (integrable_line F hF σ hy) hε₀ hε₁ σ

/-- One `y^(-σ)` bound is uniform over all `0 ≤ ε ≤ 1`.  Setting `σ=2`
gives the arithmetic summable majorant used to remove the regularizer. -/
theorem regularizedInverseLine_bound (F : ℝ → ℂ) (hF : Integrable F)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (σ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ‖regularizedInverseLine F ε σ y‖ ≤
      (‖(2 * (Real.pi : ℂ))⁻¹‖ * Real.exp (σ ^ 2) * (∫ t, ‖F t‖)) * y ^ (-σ) := by
  have hi := regularized_line_integrable F hF hε₀ hε₁ σ hy
  have hp (t : ℝ) :
      ‖(F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t‖ ≤
        (‖F t‖ * y ^ (-σ)) * Real.exp (σ ^ 2) := by
    rw [norm_mul, norm_mul, powerPhase_norm σ t hy]
    exact mul_le_mul_of_nonneg_left
      (GaussianRegularization.verticalGaussian_norm_le hε₀ hε₁ σ t)
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.le _))
  unfold regularizedInverseLine
  rw [norm_mul]
  calc
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, ‖(F t * powerPhase σ y t) * GaussianRegularization.verticalGaussian ε σ t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ∫ t, (‖F t‖ * y ^ (-σ)) * Real.exp (σ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hi.norm
          ((hF.norm.mul_const (y ^ (-σ))).mul_const (Real.exp (σ ^ 2)))
          (Filter.Eventually.of_forall hp)) (norm_nonneg _)
    _ = _ := by
      rw [integral_mul_const, integral_mul_const]
      ring

theorem uniform_tail (F : ℝ → ℂ) (hF : Integrable F) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 →
      ∀ y, 0 < y → ‖regularizedInverseLine F ε σ y‖ ≤ C * y ^ (-σ) := by
  refine ⟨‖(2 * (Real.pi : ℂ))⁻¹‖ * Real.exp (σ ^ 2) * (∫ t, ‖F t‖), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun t => norm_nonneg (F t))
  · intro ε hε₀ hε₁ y hy
    exact regularizedInverseLine_bound F hF hε₀ hε₁ σ hy

theorem regularizedInverseLine_tendsto (F : ℝ → ℂ) (hF : Integrable F)
    (ε : ℕ → ℝ) (hε₀ : ∀ n, 0 ≤ ε n) (hε₁ : ∀ n, ε n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n => regularizedInverseLine F (ε n) σ y)
      atTop (𝓝 (inverseLine F σ y)) :=
  (GaussianRegularization.regularized_integral_tendsto _
    (integrable_line F hF σ hy) ε hε₀ hε₁ hε σ).const_mul _

end ThetaGlobal.VerticalInverseBounds

#print axioms ThetaGlobal.VerticalInverseBounds.uniform_tail
#print axioms ThetaGlobal.VerticalInverseBounds.regularizedInverseLine_tendsto
