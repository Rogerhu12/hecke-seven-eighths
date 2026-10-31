import HeckeSkeleton.Moments.MOM_INV_STEP.FinalMellinTests
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileEuler
import HeckeSkeleton.Moments.MOM_BASE.CubeInversion

/-!
# The original completed test has a uniform finite Schwartz bound

On the original support [1,2], multiplication by the fixed smooth
extension of the square root is exactly `canonicalVstar`.  The map is
continuous on Schwartz space, so its Euler test seminorm is controlled
by one finite family selected before the original cutoff varies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProfile

open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOM_INV_STEP
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

def sqrtMultiplier : SchwartzMap ℝ ℂ := FinalMellinTests.weightedTest (1 / 2) 0

def completionCLM : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ sqrtMultiplier).restrictScalars ℝ

@[simp] theorem completionCLM_apply (W : SchwartzMap ℝ ℂ) (y : ℝ) :
    completionCLM W y = sqrtMultiplier y * W y :=
  SchwartzMap.smulLeftCLM_apply_apply sqrtMultiplier.hasTemperateGrowth _ _

theorem completionCLM_support (W : SchwartzMap ℝ ℂ) :
    tsupport (completionCLM W) ⊆ tsupport W := by
  change tsupport (fun y => sqrtMultiplier y * W y) ⊆ tsupport W
  exact tsupport_mul_subset_right

theorem completionCLM_eq_vstar (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (completionCLM W : ℝ → ℂ) = canonicalVstar W := by
  funext y
  by_cases hy : W y = 0
  · simp only [completionCLM_apply, canonicalVstar, hy, mul_zero]
  · obtain ⟨hl, hu⟩ := hW (subset_tsupport W (Function.mem_support.mpr hy))
    have hc := FinalMellinTests.cutoff_one (by linarith : 1 / 64 ≤ y)
      (by linarith : y ≤ 3)
    have hp : CommonKernel.columnPhase 0 (Real.log y) = 1 := by
      simp [CommonKernel.columnPhase]
    rw [completionCLM_apply, sqrtMultiplier, FinalMellinTests.weightedTest_eq,
      hc, hp, one_mul, mul_one, ← Real.sqrt_eq_rpow]
    rfl

def completedTest (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) : SmoothAnnularTest where
  toFun := completionCLM W
  smooth := (completionCLM W).smooth
  lower := 1
  upper := 2
  lower_pos := by norm_num
  upper_ge := by norm_num
  support := by
    intro y hy
    exact hW (completionCLM_support W (subset_tsupport _ hy))

@[simp] theorem completedTest_apply (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) (y : ℝ) :
    completedTest W hW y = canonicalVstar W y :=
  congrFun (completionCLM_eq_vstar W hW) y

/-- The constant and seminorm indices precede every original node test. -/
theorem exists_finite_seminorm_control (J : ℕ) (A : ℝ) :
    ∃ (q : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
        testSeminorm (canonicalVstar W) J A ≤
          C * q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, B, hB, hb⟩ := testSeminorm_finite_schwartz_control 1 2 A (by norm_num) J
  let p : Seminorm ℝ (SchwartzMap ℝ ℂ) :=
    (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp completionCLM.toLinearMap
  have hs : Continuous (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)
  obtain ⟨q, C, hC, hc⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) p (hs.comp completionCLM.continuous)
  have hCp : 0 < (C : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  refine ⟨q, B * C, mul_pos hB hCp, ?_⟩
  intro W hW
  rw [← completionCLM_eq_vstar W hW]
  exact (hb _ ((completionCLM_support W).trans hW)).trans
    ((mul_le_mul_of_nonneg_left (Seminorm.le_def.mp hc W) hB.le).trans_eq (by ring))

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProfile

end
