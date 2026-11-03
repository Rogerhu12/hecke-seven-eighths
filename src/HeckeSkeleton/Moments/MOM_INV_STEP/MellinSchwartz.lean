module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FourierSeparation
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A fixed smooth Mellin window

The cutoff and the smooth logarithm extension are chosen once.  In
particular, the oscillatory real parameter never changes the finite
Hecke background or the support of the norm test.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MellinSchwartz

open MeasureTheory
open scoped Classical ContDiff BigOperators Topology

def normBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def logBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1
  rOut := 5 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (x : ℝ) : ℂ := (normBump x : ℂ)

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff :=
  Complex.ofRealCLM.contDiff.comp normBump.contDiff

theorem cutoff_compact : HasCompactSupport cutoff :=
  normBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem cutoff_tsupport :
    tsupport cutoff = Metric.closedBall (3 / 2 : ℝ) 1 := by
  have hs : Function.support cutoff = Function.support normBump := by
    ext x
    change ((normBump x : ℝ) : ℂ) ≠ 0 ↔ normBump x ≠ 0
    exact not_congr Complex.ofReal_eq_zero
  change closure (Function.support cutoff) = _
  rw [hs]
  exact normBump.tsupport_eq

theorem cutoff_one {x : ℝ} (hx : 1 ≤ x) (hx2 : x ≤ 2) :
    cutoff x = 1 := by
  have hm : x ∈ Metric.closedBall (3 / 2 : ℝ) normBump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |x - 3 / 2| ≤ 1 / 2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold cutoff
  rw [normBump.one_of_mem_closedBall hm]
  norm_num

theorem cutoff_support_interval :
    tsupport cutoff ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
  intro x hx
  rw [cutoff_tsupport, Metric.mem_closedBall, Real.dist_eq] at hx
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  constructor <;> linarith

theorem cutoff_support_bounds {x : ℝ} (hx : x ∈ tsupport cutoff) :
    0 < x ∧ ‖x‖ ≤ 3 := by
  obtain ⟨hl, hu⟩ := cutoff_support_interval hx
  have hp : 0 < x := by linarith
  exact ⟨hp, by rw [Real.norm_eq_abs, abs_of_pos hp]; linarith⟩

theorem norm_cutoff_le_one (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [cutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg normBump.nonneg]
  exact normBump.le_one

def cutoffSchwartz : SchwartzMap ℝ ℂ :=
  cutoff_compact.toSchwartzMap cutoff_contDiff

@[simp] theorem cutoffSchwartz_apply (x : ℝ) : cutoffSchwartz x = cutoff x := rfl

def logExtension (x : ℝ) : ℝ := logBump x * Real.log x

theorem logExtension_contDiff : ContDiff ℝ ∞ logExtension := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport logBump
  · have hpos : 0 < x := by
      rw [logBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
      change |x - 3 / 2| ≤ 5 / 4 at hx
      have hl := (abs_le.mp hx).1
      linarith
    exact logBump.contDiff.contDiffAt.mul (Real.contDiffAt_log.mpr hpos.ne')
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have he : logExtension =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hz] with y hy
      change logBump y * Real.log y = 0
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem logExtension_compact : HasCompactSupport logExtension :=
  logBump.hasCompactSupport.mul_right

def logExtensionSchwartz : SchwartzMap ℝ ℝ :=
  logExtension_compact.toSchwartzMap logExtension_contDiff

@[simp] theorem logExtensionSchwartz_apply (x : ℝ) :
    logExtensionSchwartz x = logExtension x := rfl

theorem logExtension_eq_log {x : ℝ} (hx : x ∈ tsupport cutoff) :
    logExtension x = Real.log x := by
  have hm : x ∈ Metric.closedBall (3 / 2 : ℝ) logBump.rIn := by
    simpa only [cutoff_tsupport, logBump] using hx
  unfold logExtension
  rw [logBump.one_of_mem_closedBall hm, one_mul]

theorem columnPhase_eq_exp (t x : ℝ) :
    CommonKernel.columnPhase t x =
      Complex.exp (((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I) := by
  simp only [CommonKernel.columnPhase, Real.fourierChar_apply, Real.inner_apply]
  congr 2
  push_cast
  ring

/-- Restricting a smooth two-variable function to a horizontal line
does not increase the norm of an iterated derivative. -/
theorem partial_derivative_bound (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => f (y, t)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (x, t)‖ := by
  let g : ℝ × ℝ → ℂ := fun p => f (p + (0, t))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun y => f (y, t)) = g ∘ ContinuousLinearMap.inl ℝ ℝ ℝ := by
    funext y
    simp [g]
  rw [he, (ContinuousLinearMap.inl ℝ ℝ ℝ).iteratedFDeriv_comp_right hg x
    (by exact_mod_cast le_top)]
  have hb := (iteratedFDeriv ℝ n g ((ContinuousLinearMap.inl ℝ ℝ ℝ) x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ ℝ ℝ)
  simpa only [ContinuousLinearMap.norm_inl, Finset.prod_const_one, mul_one,
    g, iteratedFDeriv_comp_add_right, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using hb

end HeckeSkeleton.Moments.MOM_INV_STEP.MellinSchwartz

end
