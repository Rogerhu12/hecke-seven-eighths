import Expansion.SmoothDyadicPartition

/-! The literal complex cutoff used in the actual source and both models. -/
set_option autoImplicit false
noncomputable section
namespace Expansion.Dyadic
open scoped ContDiff

def cutoffProfile (x : ℝ) : ℂ := cutoff x

theorem cutoffProfile_smooth : ContDiff ℝ ∞ cutoffProfile := by
  unfold cutoffProfile
  exact Complex.ofRealCLM.contDiff.comp cutoff_smooth

theorem cutoffProfile_one (x : ℝ) (hx : x ≤ 1) : cutoffProfile x = 1 := by
  simp only [cutoffProfile, cutoff_one hx, Complex.ofReal_one]

theorem cutoffProfile_zero (x : ℝ) (hx : 2 ≤ x) : cutoffProfile x = 0 := by
  simp only [cutoffProfile, cutoff_zero hx, Complex.ofReal_zero]

theorem cutoffProfile_norm_le (x : ℝ) : ‖cutoffProfile x‖ ≤ 1 := by
  simpa only [cutoffProfile, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_range x).1] using (cutoff_range x).2

theorem cutoffProfile_complement_norm_le (x : ℝ) : ‖1 - cutoffProfile x‖ ≤ 1 := by
  have hnonneg : 0 ≤ 1 - cutoff x := by linarith [(cutoff_range x).2]
  have hle : 1 - cutoff x ≤ 1 := by linarith [(cutoff_range x).1]
  simpa only [cutoffProfile, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

end Expansion.Dyadic

#print axioms Expansion.Dyadic.cutoffProfile_smooth
#print axioms Expansion.Dyadic.cutoffProfile_complement_norm_le
