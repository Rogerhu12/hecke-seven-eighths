import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Analysis.TInputSeparatedProfiles
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The fixed real profile in the actual compensation prime slot

Multiplication by the total profilePower extension preserves the annular
support. At zero the original window vanishes on a neighborhood, so its
product is globally smooth although log itself is singular there. The
real exponent used below is fixed before the physical frequency.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open Set Filter
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical
open scoped ContDiff Topology

theorem support_mul_profilePower (W : ℝ → ℂ) (a : ℂ) :
    Function.support (fun y => W y * profilePower a y) = Function.support W := by
  ext y
  change W y * profilePower a y ≠ 0 ↔ W y ≠ 0
  exact ⟨left_ne_zero_of_mul, fun h => mul_ne_zero h (profilePower_ne_zero a y)⟩

/-- The zero-neighborhood argument proves global smoothness without
assuming a globally smooth logarithm or changing the physical profile. -/
theorem contDiff_mul_profilePower_annular (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (a : ℂ) :
    ContDiff ℝ ∞ (fun y => W y * profilePower a y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (fun y => W y * profilePower a y) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [gt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
      have hWy : W y = 0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp only [hWy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)
    have ha : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ) * a) x :=
      hl.mul contDiffAt_const
    simpa only [profilePower] using hW.contDiffAt.mul ha.cexp

/-- The actual z.re=17/50 line fixes the real prime profile exponent. -/
def actualCompensationPrimeProfile (g : PrimeWindowGeometry) (i : Fin g.slots)
    (y : ℝ) : ℂ :=
  (g.weight i).toFun y * profilePower (-(33 / 50 : ℂ)) y

theorem actualCompensationPrimeProfile_support (g : PrimeWindowGeometry)
    (i : Fin g.slots) :
    Function.support (actualCompensationPrimeProfile g i) ⊆ Ioo (1 : ℝ) 2 := by
  change Function.support (fun y => (g.weight i).toFun y *
    profilePower (-(33 / 50 : ℂ)) y) ⊆ _
  rw [support_mul_profilePower]
  exact g.support_annular i

theorem actualCompensationPrimeProfile_support_Icc (g : PrimeWindowGeometry)
    (i : Fin g.slots) :
    Function.support (actualCompensationPrimeProfile g i) ⊆ Icc (1 : ℝ) 2 := by
  intro y hy
  have hh := actualCompensationPrimeProfile_support g i hy
  exact ⟨hh.1.le, hh.2.le⟩

theorem contDiff_actualCompensationPrimeProfile (g : PrimeWindowGeometry)
    (i : Fin g.slots) : ContDiff ℝ ∞ (actualCompensationPrimeProfile g i) := by
  apply contDiff_mul_profilePower_annular (g.weight i).toFun (g.weight i).smooth
  intro y hy
  have hh := g.support_annular i hy
  exact ⟨hh.1.le, hh.2.le⟩

end Expansion.Project

#print axioms Expansion.Project.contDiff_mul_profilePower_annular
#print axioms Expansion.Project.actualCompensationPrimeProfile_support_Icc
#print axioms Expansion.Project.contDiff_actualCompensationPrimeProfile
