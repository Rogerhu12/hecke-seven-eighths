import HeckeSkeleton.ThetaKernel.TestMellin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
Uniform Mellin decay for the actual SmoothAnnularTest denominator, over
an arbitrary fixed compact real strip. This includes the negative w line
at a=1 and uses the project's proved Euler integration-by-parts theorem.
-/

noncomputable section
namespace HighBinBoundary.ActualDenominator

open MeasureTheory Complex HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ThetaKernel

/-- No positive-real-part restriction is needed for an annular test. -/
theorem exists_mellin_uniform_strip_bound (V : SmoothAnnularTest)
    (lower upper : ℝ) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, lower ≤ σ → σ ≤ upper →
      (1 + |t|) ^ n * ‖mellin V.toFun ((σ : ℂ) + t * I)‖ ≤ D := by
  let D : ℝ := 2 ^ n *
    ((Iint V 0 (-upper) + Iint V 0 (-lower)) +
     (Iint V n (-upper) + Iint V n (-lower)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (by positivity)
      (add_nonneg (add_nonneg (Iint_nonneg V 0 _) (Iint_nonneg V 0 _))
        (add_nonneg (Iint_nonneg V n _) (Iint_nonneg V n _)))
  refine ⟨D + 1, by linarith, ?_⟩
  intro σ t hlo hhi
  have hraw := pow_mul_norm_mellin_le V n (-σ) (-t)
  have heq : -(((-σ : ℝ) : ℂ) + (-t : ℝ) * I) = (σ : ℂ) + t * I := by
    push_cast
    ring
  rw [heq] at hraw
  have ht : |t| ≤ ‖((-σ : ℝ) : ℂ) + (-t : ℝ) * I‖ := by
    simpa using Complex.abs_im_le_norm (((-σ : ℝ) : ℂ) + (-t : ℝ) * I)
  have h0 := Iint_strip_le V 0 (show -upper ≤ -σ by linarith)
    (show -σ ≤ -lower by linarith)
  have hn := Iint_strip_le V n (show -upper ≤ -σ by linarith)
    (show -σ ≤ -lower by linarith)
  calc
    _ ≤ (1 + ‖((-σ : ℝ) : ℂ) + (-t : ℝ) * I‖) ^ n *
        ‖mellin V.toFun ((σ : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) n) (norm_nonneg _)
    _ ≤ 2 ^ n * (Iint V 0 (-σ) + Iint V n (-σ)) := hraw
    _ ≤ D := mul_le_mul_of_nonneg_left (add_le_add h0 hn) (by positivity)
    _ ≤ D + 1 := by linarith

/-- The literal denominator Mellin transform is entire. -/
theorem differentiable_mellin (V : SmoothAnnularTest) :
    Differentiable ℂ (mellin V.toFun) := by
  have h := (differentiable_mellin_neg V).comp differentiable_neg
  simpa only [Function.comp_def, neg_neg] using h

#print axioms exists_mellin_uniform_strip_bound
#print axioms differentiable_mellin

end HighBinBoundary.ActualDenominator
