import Expansion.IdealDyadicExtraction
import HeckeSkeleton.ExpansionModels.CutoffLogProfile

/-! Uniform Fourier control of the exact terminal profile used by the ideal
detector.  The original cutoff and all three scale ratios are retained. -/

set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic

open MeasureTheory
open scoped Classical ContDiff FourierTransform SchwartzMap
open ExpansionDetector.IdealCutoff ExpansionRecipe.LogProfile

theorem terminal_log_profile_eq (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (D H Y A B : ℝ) :
    logProductSchwartz (terminalProfile V V D H Y)
      (terminalProfile_smooth V V hV hV D H Y) A B =
    logSource logWindow V V logWindow_compact logWindow_smooth hV hV
      (2 * A * B / D) (A * B / Y) (A * B / H) := by
  ext y
  change logWindow y * terminalProfile V V D H Y (A * B * Real.exp y) =
    logSourceFun logWindow V V (2 * A * B / D) (A * B / Y) (A * B / H) y
  have h₁ : 2 * (A * B * Real.exp y) / D = (2 * A * B / D) * Real.exp y := by ring
  have h₂ : -(A * B * Real.exp y) / Y = -((A * B / Y) * Real.exp y) := by ring
  have h₃ : A * B * Real.exp y / H = (A * B / H) * Real.exp y := by ring
  unfold terminalProfile logSourceFun expNeg
  rw [h₁, h₂, h₃]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg]
  ring

/-- The constant is selected before every detector or dyadic scale.  Only
the fixed smooth cutoff and the Fourier moment order determine it. -/
theorem uniform_terminal_fourier_moment (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D H Y A B : ℝ,
      0 ≤ D → 0 ≤ H → 0 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logProductSchwartz (terminalProfile V V D H Y)
          (terminalProfile_smooth V V hV hV D H Y) A B)) t‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_cutoff_fourier_moment logWindow V
    logWindow_compact logWindow_smooth hV hone hzero (2 * logWindowRadius)
    (mul_nonneg (by norm_num) logWindowRadius_pos.le) logWindow_tsupport J
  refine ⟨C, hC, ?_⟩
  intro D H Y A B hD hH hY hA hB
  rw [terminal_log_profile_eq]
  exact hb _ _ _ (by positivity) (by positivity) (by positivity)

theorem uniform_terminal_fourier_mass (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D H Y A B : ℝ,
      0 ≤ D → 0 ≤ H → 0 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∫ t : ℝ, ‖(𝓕 (logProductSchwartz (terminalProfile V V D H Y)
        (terminalProfile_smooth V V hV hV D H Y) A B)) t‖) ≤ C := by
  simpa only [pow_zero, one_mul] using uniform_terminal_fourier_moment V hV hone hzero 0

end Expansion.Dyadic
