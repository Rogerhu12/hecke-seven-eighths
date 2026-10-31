import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionLines
import HeckeGeneral.Analysis.TInputSeparatedProfiles
import HeckeGeneral.Analysis.SmoothDyadicPartition

/-!
# The two actual ordinary reflection profile families

These are the compact norm profiles y^(σ-1+it) η(y), with σ later chosen
from {1/4,3/4}.  They have an exact finite ideal support independent of the
frequency, are globally smooth, and give actual `IdealTest` values at all
real scales.  The original common mask and coefficient character can be
retained when these tests replace one ordinary polynomial column.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology ContDiff

/-- An everywhere-defined version of the actual positive-ratio power
window.  Its zero set is exactly the fixed smooth cutoff's zero set. -/
def ordinaryPowerWindow (σ t y : ℝ) : ℂ :=
  (fixedDyadicWeight y : ℂ) * profilePower (idealVerticalPoint σ t - 1) y

theorem ordinaryPowerWindow_ne_zero_iff (σ t y : ℝ) :
    ordinaryPowerWindow σ t y ≠ 0 ↔ fixedDyadicWeight y ≠ 0 := by
  simp only [ordinaryPowerWindow, mul_ne_zero_iff, profilePower_ne_zero, and_true,
    ne_eq, Complex.ofReal_eq_zero]

theorem ordinaryPowerWindow_eq_cpow (σ t : ℝ) {y : ℝ} (hy : 0 < y) :
    ordinaryPowerWindow σ t y =
      (fixedDyadicWeight y : ℂ) * (y : ℂ) ^ (idealVerticalPoint σ t - 1) := by
  rw [ordinaryPowerWindow, profilePower_eq_cpow _ hy]

theorem ordinaryPowerWindow_smooth (σ t : ℝ) :
    ContDiff ℝ ∞ (ordinaryPowerWindow σ t) := by
  have hcutoff : ContDiff ℝ ∞ (fun y : ℝ => (fixedDyadicWeight y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fixedDyadicWeight
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)
  have hpower : ContDiffOn ℝ ∞ (profilePower (idealVerticalPoint σ t - 1)) (Ioi 0) :=
    Complex.contDiff_exp.comp_contDiffOn
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hlog).mul_const _)
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · exact hcutoff.contDiffAt.mul (hpower.contDiffAt (isOpen_Ioi.mem_nhds hy))
  · have hz : ordinaryPowerWindow σ t =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [gt_mem_nhds (show y < 1 / 2 by linarith)] with x hx
      simp only [ordinaryPowerWindow, fixedDyadicWeight_zero_of_le hx.le,
        Complex.ofReal_zero, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem ordinaryPowerWindow_support (σ t : ℝ) :
    Function.support (ordinaryPowerWindow σ t) ⊆ Icc (1 / 2) 2 := by
  intro y hy
  exact tsupport_fixedDyadicWeight
    (subset_tsupport fixedDyadicWeight ((ordinaryPowerWindow_ne_zero_iff σ t y).1 hy))

/-- This profile is a genuine compact smooth annular test. -/
def ordinaryPowerWindowTest (σ t : ℝ) : SmoothAnnularTest where
  toFun := ordinaryPowerWindow σ t
  smooth := ordinaryPowerWindow_smooth σ t
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  upper_ge := by norm_num
  support := ordinaryPowerWindow_support σ t

theorem ordinaryPowerWindow_norm (σ t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖ordinaryPowerWindow σ t y‖ = fixedDyadicWeight y * y ^ (σ - 1) := by
  rw [ordinaryPowerWindow_eq_cpow σ t hy, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (fixedDyadicWeight_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re, Complex.one_re,
    idealVerticalPoint_re]

theorem continuous_ordinaryPowerWindow_frequency (σ y : ℝ) :
    Continuous (fun t : ℝ => ordinaryPowerWindow σ t y) := by
  unfold ordinaryPowerWindow profilePower
  exact continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_idealVerticalPoint σ).sub continuous_const)))

variable (K : Type) [Field K] [NumberField K]

/-- The support is chosen once for a scale, before the Fourier frequency. -/
def ordinaryPowerWindowSupport (N : ℝ) : Finset (NonzeroIdeal K) :=
  if 0 < N then annularIdealSupport K (ordinaryPowerWindowTest 1 0) N else ∅

theorem mem_ordinaryPowerWindowSupport (σ t N : ℝ) (I : NonzeroIdeal K) :
    I ∈ ordinaryPowerWindowSupport K N ↔
      ordinaryPowerWindow σ t (idealNorm K I / N) ≠ 0 := by
  by_cases hN : 0 < N
  · rw [ordinaryPowerWindowSupport, if_pos hN, mem_annularIdealSupport K _ hN]
    exact (ordinaryPowerWindow_ne_zero_iff 1 0 _).trans
      (ordinaryPowerWindow_ne_zero_iff σ t _).symm
  · have hy : idealNorm K I / N ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (idealNorm_pos K I).le (le_of_not_gt hN)
    have hz : fixedDyadicWeight (idealNorm K I / N) = 0 :=
      fixedDyadicWeight_zero_of_le (by linarith)
    simp only [ordinaryPowerWindowSupport, if_neg hN, Finset.not_mem_empty,
      ordinaryPowerWindow_ne_zero_iff, hz, ne_eq, not_true_eq_false]

/-- The same genuine one-frequency family is represented by the existing
moment data, including its exact all-real-scale support specification. -/
def ordinaryPowerWindowIdealTest (σ : ℝ) : IdealTest K where
  profile _ t y := ordinaryPowerWindow σ t y
  support _ _ N := ordinaryPowerWindowSupport K N
  support_spec _ t N I := mem_ordinaryPowerWindowSupport K σ t N I

theorem annularPowerWindowSupport_eq (σ t : ℝ) {N : ℝ} (hN : 0 < N) :
    annularIdealSupport K (ordinaryPowerWindowTest σ t) N =
      ordinaryPowerWindowSupport K N := by
  ext I
  exact (mem_annularIdealSupport K _ hN I).trans
    (mem_ordinaryPowerWindowSupport K σ t N I).symm

/-- Literal finite normalized column.  The coefficient function may
already contain the original common mask and the actual Hecke coefficient. -/
def ordinaryPowerColumn (a : NonzeroIdeal K → ℂ) (σ N t : ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ ordinaryPowerWindowSupport K N,
    a I * ordinaryPowerWindow σ t (idealNorm K I / N)

theorem ordinaryPowerColumn_eq_annular (a : NonzeroIdeal K → ℂ)
    (σ t : ℝ) {N : ℝ} (hN : 0 < N) :
    ordinaryPowerColumn K a σ N t =
      (Real.sqrt N : ℂ)⁻¹ * annularIdealSum K a (ordinaryPowerWindowTest σ t) N := by
  rw [ordinaryPowerColumn, annularIdealSum, annularPowerWindowSupport_eq K σ t hN]

theorem ordinaryPowerColumn_eq_plainPolynomial
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (d : MomentData K omegaCharacter psiCharacter) (σ N t : ℝ) (u : NonzeroIdeal K) :
    ordinaryPowerColumn K
      (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
        maskValue d u I.val) σ N t =
      plainPolynomial d (ordinaryPowerWindowIdealTest K σ) u N t := by
  unfold ordinaryPowerColumn plainPolynomial ordinaryPowerWindowIdealTest
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- Actual reflected child data: replace only the selected plain test.
All arithmetic rows, every prime slot and the complete common mask remain
the original values; no new row family is postulated. -/
def ordinaryPowerChild
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (d : MomentData K omegaCharacter psiCharacter) (first : Bool) (σ frequency : ℝ) :
    MomentData K omegaCharacter psiCharacter :=
  { d with
    plainTest₁ := if first then
      (ordinaryPowerWindowIdealTest K σ).freezeTwist (fun _ => frequency) (fun _ => 0)
      else d.plainTest₁
    plainTest₂ := if first then d.plainTest₂ else
      (ordinaryPowerWindowIdealTest K σ).freezeTwist (fun _ => frequency) (fun _ => 0) }

theorem ordinaryPowerChild_preserves
    {omegaCharacter psiCharacter : HeckeCharacter K}
    (d : MomentData K omegaCharacter psiCharacter) (first : Bool) (σ frequency : ℝ) :
    (ordinaryPowerChild K d first σ frequency).commonMask = d.commonMask ∧
    (ordinaryPowerChild K d first σ frequency).rowCharacter = d.rowCharacter ∧
    (ordinaryPowerChild K d first σ frequency).geometry = d.geometry ∧
    (ordinaryPowerChild K d first σ frequency).slotCoefficient = d.slotCoefficient ∧
    ∀ a U, pairedRows (ordinaryPowerChild K d first σ frequency) a U = pairedRows d a U := by
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

end HeckeSkeleton.Moments.EngineInduction
