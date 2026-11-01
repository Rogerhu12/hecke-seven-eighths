import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalTerminal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Actual norm-power Schwartz profiles

Smooth weights supported in a fixed compact subinterval of `(0, ∞)` have
the required Schwartz realization after multiplication by `y ^ (it)`.
The construction below supplies that realization and its exact pointwise
identity; the value at every nonpositive argument remains zero.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open scoped NumberField SchwartzMap Topology ContDiff
open HeckePort.CenteredMomentVolume

theorem contDiff_normPowerWeight (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ) ^ (Complex.I * t) * W y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    have hproduct : ContDiffAt ℝ ∞
        (fun y : ℝ => (Real.log y : ℂ) * (Complex.I * t)) x :=
      hlog.mul contDiffAt_const
    have hexp := hproduct.cexp.mul hW.contDiffAt
    apply hexp.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
      ← Complex.ofReal_log (le_of_lt hy)]
  · have hxa : x < a := lt_of_le_of_lt (le_of_not_gt hx) ha
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
    have hw : W y = 0 := by
      by_contra h
      exact (not_le_of_gt hy) (hs h).1
    simp only [hw, mul_zero]

/-- The actual Schwartz function `y ↦ y ^ (it) W(y)`. -/
def normPowerSchwartzProfile (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs).mul_left
    (f := fun y : ℝ => (y : ℂ) ^ (Complex.I * t))).toSchwartzMap
      (contDiff_normPowerWeight W a b ha hs hW t)

@[simp] theorem normPowerSchwartzProfile_apply (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t y : ℝ) :
    normPowerSchwartzProfile W a b ha hs hW t y =
      (y : ℂ) ^ (Complex.I * t) * W y := rfl

theorem norm_normPowerSchwartzProfile (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t y : ℝ) :
    ‖normPowerSchwartzProfile W a b ha hs hW t y‖ = ‖W y‖ :=
  HeckePort.Moments.Twist.profile_norm W (normPowerSchwartzProfile W a b ha hs hW)
    (normPowerSchwartzProfile_apply W a b ha hs hW)
    (fun x hx => ha.trans_le (hs hx).1) t y

theorem support_normPowerSchwartzProfile (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerSchwartzProfile W a b ha hs hW t : ℝ → ℂ) ⊆
      Set.Icc a b :=
  (HeckePort.Moments.Twist.profile_support W (normPowerSchwartzProfile W a b ha hs hW)
    (normPowerSchwartzProfile_apply W a b ha hs hW) t).trans hs

variable {K : Type*} [Field K] [NumberField K]

/-- Build the terminal profile family directly from smooth compact weights.
Only the analytic error functional's seminorm bound remains an input. -/
def ExceptionalProfiles.ofSmoothWeights {Ψ : Ideal (𝓞 K) → ℂ}
    (V : IdealVolumeInput K Ψ) {ι : Type*}
    (W : ι → ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hs : ∀ i, Function.support (W i) ⊆ Set.Icc a b)
    (hW : ∀ i, ContDiff ℝ ∞ (W i))
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hbound : ∀ i y, ‖W i y‖ ≤ p i)
    (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (herr : ∀ i t,
      V.error (normPowerSchwartzProfile (W i) a b ha (hs i) (hW i) t) ≤
        D * p i * (1 + ‖t‖) ^ n) : ExceptionalProfiles V ι where
  weight := W
  lower := a
  upper := b
  lower_pos := ha
  upper_nonneg := hb
  seminorm := p
  seminorm_nonneg := hp
  support := hs
  norm_bound := hbound
  profile i := normPowerSchwartzProfile (W i) a b ha (hs i) (hW i)
  profile_eq i := normPowerSchwartzProfile_apply (W i) a b ha (hs i) (hW i)
  order := n
  errorConstant := D
  errorConstant_nonneg := hD
  error_bound := herr

end HeckeSkeleton.Moments.MOM_PRIME
