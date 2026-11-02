import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceFrame
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed numerical boxes for the actual two-pass source

These are the scalar formulas of the primitive engine, with no source,
kernel or terminal estimate stored as data. Both physical cutoffs use
the merged `firstTailCutoffExponent` and `tailDecayForWidth` functions.
The explicit power threshold replaces only a noncanonical choice of
a sufficiently large real number; its numerical obligations remain
visible below.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep
open scoped Classical

def powerThreshold (coefficient exponent : ℝ) : ℝ :=
  max 2 ((max 1 coefficient) ^ exponent⁻¹)

theorem powerThreshold_gt_one (coefficient exponent : ℝ) :
    1 < powerThreshold coefficient exponent :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem powerThreshold_spec (coefficient exponent Z : ℝ)
    (hexponent : 0 < exponent) (hZ : powerThreshold coefficient exponent ≤ Z) :
    coefficient ≤ Z ^ exponent := by
  sorry

def originalFirstPhysicalDegree (cap : ℕ) (bound : ℝ) : ℝ :=
  2 * bound * ((2 * (cap + 2) : ℕ) : ℝ) + 3 * bound

namespace CanonicalOriginalParentFactory

structure FixedBox where
  cap : ℕ
  widthMax paddingMax : ℝ
  width_nonneg : 0 ≤ widthMax
  padding_nonneg : 0 ≤ paddingMax
  annulus : ℝ
  annulus_ge_one : 1 ≤ annulus
  loss : ℝ
  loss_pos : 0 < loss
  loss_le_one : loss ≤ 1
  tailSaving : ℝ
  tailSaving_nonneg : 0 ≤ tailSaving
  decay : ℝ
  decay_gt_one : 1 < decay

namespace FixedBox

def plainBound (b : FixedBox) : ℝ := b.widthMax + b.paddingMax
def columnBound (b : FixedBox) : ℝ := 3 * b.plainBound + 1
def tailDegree (b : FixedBox) : ℝ := originalFirstPhysicalDegree b.cap b.columnBound
def cutoffExponent (b : FixedBox) : ℝ :=
  firstTailCutoffExponent b.tailDegree b.tailSaving b.decay
def cutoff (b : FixedBox) (Z : ℝ) : ℝ := Z ^ b.cutoffExponent
def rowBound (b : FixedBox) : ℝ := max 0 (b.cutoffExponent + 3 * b.columnBound)
def threshold (b : FixedBox) : ℝ := powerThreshold (b.annulus ^ (b.cap + 2)) b.loss

theorem plainBound_nonneg (b : FixedBox) : 0 ≤ b.plainBound :=
  add_nonneg b.width_nonneg b.padding_nonneg

theorem columnBound_nonneg (b : FixedBox) : 0 ≤ b.columnBound := by
  have h := b.plainBound_nonneg
  unfold columnBound
  positivity

theorem rowBound_nonneg (b : FixedBox) : 0 ≤ b.rowBound := le_max_left _ _

theorem cutoff_ge_one (b : FixedBox) {Z : ℝ} (hZ : 1 ≤ Z) : 1 ≤ b.cutoff Z :=
  Real.one_le_rpow hZ (firstTailCutoffExponent_nonneg _ _ _ b.decay_gt_one)

theorem threshold_gt_one (b : FixedBox) : 1 < b.threshold := powerThreshold_gt_one _ _

theorem annulus_bound (b : FixedBox) {Z : ℝ} (hZ : b.threshold ≤ Z) :
    b.annulus ^ (b.cap + 2) ≤ Z ^ b.loss :=
  powerThreshold_spec _ _ _ b.loss_pos hZ

end FixedBox
end CanonicalOriginalParentFactory

namespace CanonicalOriginalTerminalPowers

def tailDegree (k : ℕ) (totalBound coarseBound frozenBound radiusBound : ℝ) : ℝ :=
  2 * coarseBound * ((k + 1 : ℕ) : ℝ) + totalBound + 2 * frozenBound + 4 +
    max (2 * coarseBound) radiusBound

def primitiveDegree (cap : ℕ) (lengthBound columnBound step loss cutoffExponent : ℝ) : ℝ :=
  tailDegree (2 * (cap + 2)) lengthBound columnBound (columnBound + 7 * (step / 3))
    (4 * max lengthBound columnBound + (2 * loss + cutoffExponent) + 2 * step)

def primitiveCutoff (cap : ℕ) (lengthBound columnBound step loss cutoffExponent
    saving decay Z : ℝ) : ℝ :=
  Z ^ firstTailCutoffExponent
    (primitiveDegree cap lengthBound columnBound step loss cutoffExponent) saving decay

end CanonicalOriginalTerminalPowers

namespace CanonicalPrimitiveEngineChoices

structure Box where
  cap : ℕ
  widthMax paddingMax lo hi step ε : ℝ
  width_nonneg : 0 ≤ widthMax
  padding_nonneg : 0 ≤ paddingMax
  lo_pos : 0 < lo
  lo_le_one : lo ≤ 1
  hi_ge_one : 1 ≤ hi
  step_pos : 0 < step
  ε_pos : 0 < ε

namespace Box

def lengthBound (b : Box) : ℝ := b.widthMax + b.paddingMax
def columnBound (b : Box) : ℝ := 3 * b.lengthBound + 1
def normBound (b : Box) : ℝ := max b.lengthBound b.columnBound
def loss (b : Box) : ℝ :=
  min (1 : ℝ) (min (b.step / 64) ((b.ε / ((b.cap : ℝ) + 1)) / 4096))
def error (b : Box) : ℝ := 3 * b.loss
def tilt (b : Box) : ℝ := min (1 / 4 : ℝ) ((b.ε / 16) / (16 * (b.normBound + 1)))
def saving (b : Box) : ℝ := 2 * b.normBound + 1
def firstDegree (b : Box) : ℝ := originalFirstPhysicalDegree b.cap b.columnBound
def secondDegree (b : Box) : ℝ :=
  CanonicalOriginalTerminalPowers.primitiveDegree
    b.cap b.lengthBound b.columnBound b.step b.loss b.loss
def firstDecay (b : Box) : ℝ := tailDecayForWidth b.firstDegree b.saving b.loss
def secondDecay (b : Box) : ℝ := tailDecayForWidth b.secondDegree b.saving b.loss
def rawNormBound (b : Box) : ℝ := b.widthMax + b.columnBound + 3 * b.loss
def rowBound (b : Box) : ℝ := 2 * b.lengthBound + 2 * b.columnBound + 3 * b.loss
def sourceWidth (b : Box) : ℝ := max b.widthMax (b.columnBound + 2 * (b.step / 3))
def volumeLoss (b : Box) : ℝ := b.ε / 64
def maskExponent (b : Box) : ℝ := 2 * b.sourceWidth + 3 * b.loss + 1

theorem lengthBound_nonneg (b : Box) : 0 ≤ b.lengthBound :=
  add_nonneg b.width_nonneg b.padding_nonneg

theorem columnBound_nonneg (b : Box) : 0 ≤ b.columnBound := by
  have h := b.lengthBound_nonneg
  unfold columnBound
  positivity

theorem normBound_nonneg (b : Box) : 0 ≤ b.normBound :=
  b.lengthBound_nonneg.trans (le_max_left _ _)

theorem loss_pos (b : Box) : 0 < b.loss := by
  have hs := b.step_pos
  have he := b.ε_pos
  unfold loss
  positivity

theorem loss_le_one (b : Box) : b.loss ≤ 1 := min_le_left _ _
theorem loss_le_step (b : Box) : b.loss ≤ b.step / 64 :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem loss_le_ε (b : Box) : b.loss ≤ b.ε / 4096 := by
  sorry

theorem error_pos (b : Box) : 0 < b.error := mul_pos (by norm_num) b.loss_pos

theorem tilt_pos (b : Box) : 0 < b.tilt := by
  have h := b.normBound_nonneg
  have he := b.ε_pos
  unfold tilt
  positivity

theorem tilt_le_quarter (b : Box) : b.tilt ≤ 1 / 4 := min_le_left _ _
theorem tilt_le_half (b : Box) : b.tilt ≤ 1 / 2 :=
  b.tilt_le_quarter.trans (by norm_num)

theorem saving_pos (b : Box) : 0 < b.saving := by
  have h := b.normBound_nonneg
  unfold saving
  positivity

theorem firstDecay_gt_one (b : Box) : 1 < b.firstDecay :=
  tailDecayForWidth_gt_one _ _ _ b.loss_pos
theorem secondDecay_gt_one (b : Box) : 1 < b.secondDecay :=
  tailDecayForWidth_gt_one _ _ _ b.loss_pos

def firstBox (b : Box) : CanonicalOriginalParentFactory.FixedBox where
  cap := b.cap
  widthMax := b.widthMax
  paddingMax := b.paddingMax
  width_nonneg := b.width_nonneg
  padding_nonneg := b.padding_nonneg
  annulus := b.hi
  annulus_ge_one := b.hi_ge_one
  loss := b.loss
  loss_pos := b.loss_pos
  loss_le_one := b.loss_le_one
  tailSaving := b.saving
  tailSaving_nonneg := b.saving_pos.le
  decay := b.firstDecay
  decay_gt_one := b.firstDecay_gt_one

abbrev base (b : Box) : CanonicalOriginalParentFactory.FixedBox := b.firstBox
abbrev delta (b : Box) : ℝ := b.tilt
def firstCutoff (b : Box) (Z : ℝ) : ℝ := b.firstBox.cutoff Z
def secondCutoff (b : Box) (Z : ℝ) : ℝ :=
  CanonicalOriginalTerminalPowers.primitiveCutoff
    b.cap b.lengthBound b.columnBound b.step b.loss b.loss b.saving b.secondDecay Z

theorem firstCutoff_ge_one (b : Box) {Z : ℝ} (hZ : 1 ≤ Z) :
    1 ≤ b.firstCutoff Z := b.firstBox.cutoff_ge_one hZ

theorem firstCutoff_le (b : Box) {Z : ℝ} (hZ : 1 ≤ Z) :
    b.firstCutoff Z ≤ Z ^ b.loss :=
  Real.rpow_le_rpow_of_exponent_le hZ
    (firstTailCutoffExponent_le_width _ _ _ _ b.loss_pos le_rfl)

theorem secondCutoff_ge_one (b : Box) {Z : ℝ} (hZ : 1 ≤ Z) :
    1 ≤ b.secondCutoff Z :=
  Real.one_le_rpow hZ (firstTailCutoffExponent_nonneg _ _ _ b.secondDecay_gt_one)

theorem secondCutoff_le (b : Box) {Z : ℝ} (hZ : 1 ≤ Z) :
    b.secondCutoff Z ≤ Z ^ b.loss :=
  Real.rpow_le_rpow_of_exponent_le hZ
    (firstTailCutoffExponent_le_width _ _ _ _ b.loss_pos le_rfl)

theorem rawNormBound_nonneg (b : Box) : 0 ≤ b.rawNormBound := by
  have h₁ := b.width_nonneg
  have h₂ := b.columnBound_nonneg
  have h₃ := b.loss_pos.le
  unfold rawNormBound
  positivity

theorem rowBound_nonneg (b : Box) : 0 ≤ b.rowBound := by
  have h₁ := b.lengthBound_nonneg
  have h₂ := b.columnBound_nonneg
  have h₃ := b.loss_pos.le
  unfold rowBound
  positivity

theorem sourceWidth_nonneg (b : Box) : 0 ≤ b.sourceWidth :=
  b.width_nonneg.trans (le_max_left _ _)
theorem volumeLoss_pos (b : Box) : 0 < b.volumeLoss := div_pos b.ε_pos (by norm_num)
theorem maskExponent_nonneg (b : Box) : 0 ≤ b.maskExponent := by
  have h₁ := b.sourceWidth_nonneg
  have h₂ := b.loss_pos.le
  unfold maskExponent
  positivity

/-- Both annuli and the actual excluded-prime count are paid here. -/
def threshold (b : Box) : ℝ := max
  (powerThreshold (max (b.hi ^ (b.cap + 2)) ((b.lo ^ (b.cap + 2))⁻¹)) b.loss)
  (powerThreshold
    (2 * (b.rowBound / ((b.step / 3) / 2) + b.columnBound / ((b.step / 3) / 2)))
    (b.step / 3 - b.loss))

def fullThreshold (b : Box) : ℝ := max b.threshold
  (max b.firstBox.threshold
    (max (max 2 (Real.exp (2 * Real.log b.hi / b.error)))
      (powerThreshold (max (b.hi ^ (2 * b.cap)) b.hi) b.loss)))

theorem threshold_gt_one (b : Box) : 1 < b.threshold :=
  (powerThreshold_gt_one _ _).trans_le (le_max_left _ _)
theorem fullThreshold_gt_one (b : Box) : 1 < b.fullThreshold :=
  b.threshold_gt_one.trans_le (le_max_left _ _)

end Box
end CanonicalPrimitiveEngineChoices
end HeckeSkeleton.Moments.EngineStepV2
