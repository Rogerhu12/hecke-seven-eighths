import ExpansionInterfaces.LogDividedAnnularProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive residue mass and absorption for the original prime windows

A real, nonnegative, nonzero smooth annular window has positive ordinary
mass. Its exact inverse-log Mellin residue retains that mass up to the
factor `2 log X`. The power-saving contour error, higher prime powers, and
any fixed finite deletion are eventually smaller than half this main term.
All constants precede the later prime scale.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open Set Filter MeasureTheory Asymptotics
open ExpansionInterfaces.Mellin PrimeCancellationLogWindow
open scoped Classical Topology ContDiff

theorem annularProfile_compact (W : AnnularProfile) : HasCompactSupport W.function :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc W.supported

theorem annularProfile_integrable (W : AnnularProfile) : Integrable W.function :=
  W.smooth.continuous.integrable_of_hasCompactSupport (annularProfile_compact W)

/-- At one, the actual Mellin measure is ordinary positive-line Lebesgue measure. -/
theorem mellin_one_eq_integral_of_window (f : ℝ → ℂ)
    (hs : Function.support f ⊆ Icc (1 : ℝ) 2) :
    mellin f 1 = ∫ y : ℝ, f y := by
  simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  by_contra hne
  have hh := (hs hne).1
  have hy' : y ≤ 0 := le_of_not_gt hy
  linarith

theorem annularProfile_real_mass_pos (W : AnnularProfile)
    (hre : ∀ y, (W.function y).im = 0) (hnn : ∀ y, 0 ≤ (W.function y).re)
    (hne : ∃ y, W.function y ≠ 0) :
    0 < ∫ y : ℝ, (W.function y).re := by
  obtain ⟨y, hy⟩ := hne
  have hyr : (W.function y).re ≠ 0 := by
    intro hzero
    apply hy
    exact Complex.ext hzero (hre y)
  exact integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp W.smooth.continuous)
    (annularProfile_integrable W).re hnn hyr

theorem logWindow_real_lower (W : AnnularProfile)
    (hnn : ∀ y, 0 ≤ (W.function y).re)
    (hs : Function.support W.function ⊆ Icc (1 : ℝ) 2)
    {X : ℝ} (hX : 2 ≤ X) (y : ℝ) :
    (W.function y).re / (2 * Real.log X) ≤ (logWindow X W.function y).re := by
  by_cases hWy : W.function y = 0
  · simp only [hWy, Complex.zero_re, zero_div, logWindow, le_refl]
  have hy := hs hWy
  have hXpos : 0 < X := by linarith
  have hypos : 0 < y := by linarith [hy.1]
  have hscaled : 0 < Real.log (X * y) := log_scaled_pos hX hy.1
  have hly : Real.log y ≤ Real.log X :=
    Real.log_le_log hypos (hy.2.trans hX)
  have hup : Real.log (X * y) ≤ 2 * Real.log X := by
    rw [Real.log_mul hXpos.ne' hypos.ne']
    linarith
  rw [logWindow, Complex.div_ofReal_re]
  exact div_le_div_of_nonneg_left (hnn y) hscaled hup

/-- The constant is fixed by the original physical window alone. -/
theorem exists_logWindow_mellin_one_lower (W : AnnularProfile)
    (hre : ∀ y, (W.function y).im = 0) (hnn : ∀ y, 0 ≤ (W.function y).re)
    (hne : ∃ y, W.function y ≠ 0)
    (hs : Function.support W.function ⊆ Ioo (1 : ℝ) 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, Real.exp 4 ≤ X →
      c / Real.log X ≤ (mellin (logWindow X W.function) 1).re := by
  let mass : ℝ := ∫ y : ℝ, (W.function y).re
  have hmass : 0 < mass := annularProfile_real_mass_pos W hre hnn hne
  have hs' : Function.support W.function ⊆ Icc (1 : ℝ) 2 :=
    hs.trans Ioo_subset_Icc_self
  refine ⟨mass / 2, div_pos hmass (by norm_num), ?_⟩
  intro X hX
  have hX2 := two_le_exp_four.trans hX
  have hV : Integrable (logWindow X W.function) :=
    (contDiff_logWindow hX2 W.smooth hs').continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_logWindow X W.function hs')
  have hreal : (∫ y : ℝ, logWindow X W.function y).re =
      ∫ y : ℝ, (logWindow X W.function y).re :=
    (Complex.reCLM.integral_comp_comm hV).symm
  rw [mellin_one_eq_integral_of_window _ (support_logWindow_subset_Icc X W.function hs'), hreal]
  have hi := integral_mono ((annularProfile_integrable W).re.div_const (2 * Real.log X))
    hV.re (logWindow_real_lower W hnn hs' hX2)
  rw [integral_div] at hi
  convert hi using 1 <;> dsimp [mass] <;> ring

/-- A fixed power saving, square-root term, and finite deletion can all be
absorbed into half the positive `X/log X` residue term. -/
theorem eventually_primeWindow_error_le (c C B D : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ X : ℝ in atTop,
      C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X + D ≤ (c / 2) * X / Real.log X := by
  let M : ℝ := C + B + D
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlittle : (fun X : ℝ => M * Real.log X) =o[atTop]
      (fun X : ℝ => X ^ (1 / 64 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64)).const_mul_left M
  filter_upwards [hlittle.bound (div_pos hc (by norm_num : (0 : ℝ) < 2)),
    eventually_ge_atTop (2 : ℝ)]
    with X hlog hX
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog' : M * Real.log X ≤ (c / 2) * X ^ (1 / 64 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM hlpos.le),
      abs_of_nonneg (Real.rpow_nonneg hXpos.le _)] using hlog
  have hsqrt : Real.sqrt X ≤ X ^ (63 / 64 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hone : 1 ≤ X ^ (63 / 64 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hsum : C * X ^ (63 / 64 : ℝ) + B * Real.sqrt X + D ≤
      M * X ^ (63 / 64 : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hsqrt hB
    have hd := le_mul_of_one_le_right hD hone
    dsimp [M]
    nlinarith
  apply hsum.trans
  apply (le_div_iff₀ hlpos).mpr
  have hh := mul_le_mul_of_nonneg_right hlog' (Real.rpow_nonneg hXpos.le (63 / 64 : ℝ))
  have hp : X ^ (1 / 64 : ℝ) * X ^ (63 / 64 : ℝ) = X := by
    rw [← Real.rpow_add hXpos]
    norm_num
  calc
    _ = (M * Real.log X) * X ^ (63 / 64 : ℝ) := by ring
    _ ≤ ((c / 2) * X ^ (1 / 64 : ℝ)) * X ^ (63 / 64 : ℝ) := hh
    _ = (c / 2) * X := by rw [mul_assoc, hp]

end Expansion.Project

#print axioms Expansion.Project.exists_logWindow_mellin_one_lower
#print axioms Expansion.Project.eventually_primeWindow_error_le
