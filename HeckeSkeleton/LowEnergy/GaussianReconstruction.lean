import HeckeGeneral.Analysis.SmoothIntegerPartition
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!+# Actual Gaussian annuli and absolutely convergent series

The cutoff is the explicitly constructed `fixedIntegerCutoff` in the input
project.  Every annulus has the same compact support, bounded away from zero.
The double-series theorem derives its absolute convergence from that of the
original series: there is no separate Fubini or reflection assumption.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.Gaussian

open HeckeGeneral.Analysis Filter
open scoped BigOperators Topology ContDiff

/-- A normalized annulus on the fixed multiplicative interval `[exp(-1),exp(1)]`. -/
def annulus (k : ℤ) (x : ℝ) : ℂ :=
  if 0 < x then
    logGaussianNormalization * (cutoffGaussianAnnulus fixedIntegerCutoff k (Real.log x) : ℂ)
  else 0

theorem annulus_of_pos (k : ℤ) {x : ℝ} (hx : 0 < x) :
    annulus k x = logGaussianNormalization *
      (realLogGaussian ((k : ℝ) + Real.log x) * fixedIntegerCutoff (Real.log x) : ℝ) := by
  simp [annulus, hx, cutoffGaussianAnnulus]

theorem annulus_zero_of_lt (k : ℤ) {x : ℝ} (hx : x < Real.exp (-1)) :
    annulus k x = 0 := by
  by_cases hpos : 0 < x
  · rw [annulus_of_pos k hpos]
    have hl : Real.log x ≤ -1 :=
      (Real.log_le_iff_le_exp hpos).2 hx.le
    rw [fixedIntegerCutoff_zero_of_le hl, mul_zero, Complex.ofReal_zero, mul_zero]
  · simp [annulus, hpos]

theorem annulus_zero_of_gt (k : ℤ) {x : ℝ} (hx : Real.exp 1 < x) :
    annulus k x = 0 := by
  have hpos : 0 < x := (Real.exp_pos 1).trans hx
  rw [annulus_of_pos k hpos]
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hpos).2 hx.le
  rw [fixedIntegerCutoff_zero_of_ge hl, mul_zero, Complex.ofReal_zero, mul_zero]

theorem annulus_support (k : ℤ) :
    Function.support (annulus k) ⊆ Set.Icc (Real.exp (-1)) (Real.exp 1) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (annulus_zero_of_lt k (lt_of_not_ge h))
  · by_contra h
    exact hx (annulus_zero_of_gt k (lt_of_not_ge h))

theorem annulus_smooth (k : ℤ) : ContDiff ℝ ∞ (annulus k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hx.ne'
    have hreal : ContDiffAt ℝ ∞
        (fun y => cutoffGaussianAnnulus fixedIntegerCutoff k (Real.log y)) x := by
      unfold cutoffGaussianAnnulus
      exact ((contDiff_realLogGaussian.contDiffAt.comp x
        (contDiffAt_const.add hlog)).mul
        (contDiff_fixedIntegerCutoff.contDiffAt.comp x hlog))
    have hc : ContDiffAt ℝ ∞
        (fun y => logGaussianNormalization *
          (cutoffGaussianAnnulus fixedIntegerCutoff k (Real.log y) : ℂ)) x :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp [annulus, hy]
  · have hx' : x < Real.exp (-1) :=
      lt_of_le_of_lt (le_of_not_gt hx) (Real.exp_pos _)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx'] with y hy
    exact annulus_zero_of_lt k hy

theorem logGaussianProfile_eq_real (x : ℝ) :
    logGaussianProfile x = logGaussianNormalization * (realLogGaussian (Real.log x) : ℂ) := by
  unfold logGaussianProfile logarithmicGaussian realLogGaussian
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

/-- Rescaling restores exactly the original Gaussian, multiplied by the partition cutoff. -/
theorem annulus_rescale (k : ℤ) {x : ℝ} (hx : 0 < x) :
    annulus k (x / Real.exp (k : ℝ)) =
      logGaussianProfile x * (fixedIntegerCutoff (Real.log x - k) : ℂ) := by
  rw [annulus_of_pos k (div_pos hx (Real.exp_pos _)), Real.log_div hx.ne'
    (Real.exp_ne_zero _), Real.log_exp, logGaussianProfile_eq_real]
  rw [show (k : ℝ) + (Real.log x - k) = Real.log x by ring]
  push_cast
  ring

theorem cutoff_summable (x : ℝ) : Summable (fun k : ℤ => fixedIntegerCutoff (x - k)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋, ⌊x⌋ + 1})
  exact fixedIntegerCutoff_shift_zero x

theorem cutoff_complex_sum (x : ℝ) :
    (∑' k : ℤ, (fixedIntegerCutoff (x - k) : ℂ)) = 1 := by
  rw [← Complex.ofReal_tsum, fixedIntegerCutoff_partition]
  rfl

theorem annulus_partition {x : ℝ} (hx : 0 < x) :
    (∑' k : ℤ, annulus k (x / Real.exp (k : ℝ))) = logGaussianProfile x := by
  simp_rw [annulus_rescale _ hx]
  rw [tsum_mul_left, cutoff_complex_sum, mul_one]

theorem norm_cutoff_product (z : ℂ) (x : ℝ) (k : ℤ) :
    ‖z * (fixedIntegerCutoff (x - k) : ℂ)‖ =
      ‖z‖ * fixedIntegerCutoff (x - k) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fixedIntegerCutoff_nonneg _)]

/-- Partitioning a term preserves its entire absolute mass, exactly. -/
theorem cutoff_absolute_mass (z : ℂ) (x : ℝ) :
    (∑' k : ℤ, ‖z * (fixedIntegerCutoff (x - k) : ℂ)‖) = ‖z‖ := by
  simp_rw [norm_cutoff_product]
  rw [tsum_mul_left, fixedIntegerCutoff_partition, mul_one]

theorem split_series_absolute {α : Type*} (f : α → ℂ) (x : α → ℝ)
    (hf : Summable (fun a => ‖f a‖)) :
    Summable (fun p : α × ℤ => ‖f p.1 * (fixedIntegerCutoff (x p.1 - p.2) : ℂ)‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  constructor
  · intro a
    simpa only [norm_cutoff_product] using (cutoff_summable (x a)).mul_left ‖f a‖
  · simpa only [cutoff_absolute_mass] using hf

theorem split_outer_summable {α : Type*} (f : α → ℂ) (x : α → ℝ)
    (hf : Summable (fun a => ‖f a‖)) :
    Summable (fun k : ℤ => ∑' a,
      f a * (fixedIntegerCutoff (x a - k) : ℂ)) := by
  exact (split_series_absolute f x hf).of_norm.prod_symm.prod

/-- Fubini for the actual split series follows from the original absolute convergence. -/
theorem split_series_tsum {α : Type*} (f : α → ℂ) (x : α → ℝ)
    (hf : Summable (fun a => ‖f a‖)) :
    (∑' a, f a) =
      ∑' k : ℤ, ∑' a, f a * (fixedIntegerCutoff (x a - k) : ℂ) := by
  have hs : Summable (fun p : α × ℤ =>
      f p.1 * (fixedIntegerCutoff (x p.1 - p.2) : ℂ)) :=
    (split_series_absolute f x hf).of_norm
  calc
    (∑' a, f a) = ∑' a, ∑' k : ℤ,
        f a * (fixedIntegerCutoff (x a - k) : ℂ) := by
      apply tsum_congr
      intro a
      rw [tsum_mul_left, cutoff_complex_sum, mul_one]
    _ = _ := hs.tsum_comm.symm

#print axioms annulus_smooth
#print axioms annulus_partition
#print axioms split_series_absolute
#print axioms split_series_tsum

end HeckeSkeleton.LowEnergy.Gaussian
