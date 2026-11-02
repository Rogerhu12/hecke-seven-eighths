import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalParentFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEngineSmallParameters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPairAllowanceProduction

set_option linter.unusedSectionVars false

/-!
# Fixed numerical choices before the original engine sources

This box contains only the original bounded ranges and the requested
step and power loss. Both physical cutoffs, the common logarithmic tilt,
annulus threshold and one prime pool are then chosen internally. No
source, parent inequality, terminal estimate or family bound is a field.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices

open NumberField DedekindZetaZeroFree LocalFiniteSums
open CanonicalEngineSmallParameters

/-- Fixed original numerical ranges. The lower annulus is retained
because the sharp central normalization uses its actual inverse norm. -/
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

variable (b : Box)

def lengthBound : ℝ := b.widthMax + b.paddingMax

def columnBound : ℝ := 3 * b.lengthBound + 1

def normBound : ℝ := max b.lengthBound b.columnBound

/-- Divide the per-slot boundary budget by the fixed slot cap before
any allocation is selected. This also pays the sum of removed-slot
errors in the exceptional source. -/
def loss : ℝ := boundary b.step (b.ε / ((b.cap : ℝ) + 1))

/-- The allocation allowance pays both original annuli and the
actual cutoff. It is larger than each physical boundary loss. -/
def error : ℝ := 3 * b.loss

def tilt : ℝ := CanonicalEngineSmallParameters.tilt b.normBound b.ε

def saving : ℝ := tailSaving b.normBound

theorem lengthBound_nonneg : 0 ≤ b.lengthBound := by
  sorry

theorem columnBound_nonneg : 0 ≤ b.columnBound := by
  sorry

theorem normBound_nonneg : 0 ≤ b.normBound := by
  sorry

theorem loss_pos : 0 < b.loss := by
  sorry

theorem loss_le_one : b.loss ≤ 1 := by
  sorry

theorem loss_le_step : b.loss ≤ b.step / 64 := by
  sorry

theorem loss_le_ε : b.loss ≤ b.ε / 4096 := by
  sorry

theorem cap_mul_loss_le_ε : (b.cap : ℝ) * b.loss ≤ b.ε / 4096 := by
  sorry

theorem error_pos : 0 < b.error := by
  sorry

theorem support_error_le : 2 * b.loss + b.loss ≤ b.error := by
  sorry

theorem cap_mul_error_le : (b.cap : ℝ) * b.error ≤ b.ε / 64 := by
  sorry

theorem tilt_pos : 0 < b.tilt := by
  sorry

theorem tilt_le_quarter : b.tilt ≤ 1 / 4 := by
  sorry

theorem tilt_le_half : b.tilt ≤ 1 / 2 := by
  sorry

theorem saving_pos : 0 < b.saving := by
  sorry

theorem saving_ge_column : 2 * b.columnBound ≤ b.saving := by
  sorry

def firstDegree : ℝ := originalFirstPhysicalDegree b.cap b.columnBound

def secondDegree : ℝ := CanonicalOriginalTerminalPowers.primitiveDegree
  b.cap b.lengthBound b.columnBound b.step b.loss b.loss

def firstDecay : ℝ := tailDecayForWidth b.firstDegree b.saving b.loss

def secondDecay : ℝ := tailDecayForWidth b.secondDegree b.saving b.loss

theorem firstDecay_gt_one : 1 < b.firstDecay := by
  sorry

theorem secondDecay_gt_one : 1 < b.secondDecay := by
  sorry

/-- The first cutoff uses its own original physical degree. -/
def firstBox : CanonicalOriginalParentFactory.FixedBox where
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

theorem firstCutoffExponent_le : b.firstBox.cutoffExponent ≤ b.loss := by
  sorry

theorem firstCutoff_le (Z : ℝ) (hZ : 1 ≤ Z) : b.firstBox.cutoff Z ≤ Z ^ b.loss := by
  sorry

/-- The second cutoff keeps the full original main and error degree. -/
def secondCutoff (Z : ℝ) : ℝ :=
  CanonicalOriginalTerminalPowers.primitiveCutoff b.cap b.lengthBound b.columnBound
    b.step b.loss b.loss b.saving b.secondDecay Z

theorem secondCutoff_ge_one (Z : ℝ) (hZ : 1 ≤ Z) : 1 ≤ b.secondCutoff Z := by
  sorry

theorem secondCutoff_le (Z : ℝ) (hZ : 1 ≤ Z) : b.secondCutoff Z ≤ Z ^ b.loss := by
  sorry

theorem width_margin : 2 * (2 * b.loss + b.loss) ≤ b.step := by
  sorry

theorem pool_separation : b.loss < b.step / 6 ∧ b.loss < b.step / 3 := by
  sorry

/-- All raw second-zero small powers fit in the same requested loss;
the principal padding and step remain visible to the induction. -/
theorem secondZero_loss :
    (2 * b.loss + b.loss) + 2 * b.loss +
      (4 * b.normBound + 2) * b.tilt +
      2 * (b.normBound + 1) * b.tilt + b.loss + b.ε / 8 ≤ b.ε / 4 := by
  sorry

theorem direct_mass_loss :
    9 * (b.ε / 16) / 4 + 5 * b.error / 3 + b.loss ≤ b.ε / 4 := by
  sorry

theorem pooled_mass_loss :
    9 * (b.ε / 16) / 4 + b.loss + 5 * b.error / 3 + b.loss ≤ b.ε / 4 := by
  sorry

def rawNormBound : ℝ := b.widthMax + b.columnBound + 3 * b.loss

theorem rawNormBound_nonneg : 0 ≤ b.rawNormBound := by
  sorry

/-- The same coarse row box is used on both first Gauss sides. -/
def rowBound : ℝ := 2 * b.lengthBound + 2 * b.columnBound + 2 * b.loss + b.loss

theorem rowBound_nonneg : 0 ≤ b.rowBound := by
  sorry

private theorem exists_power_threshold (C exponent : ℝ) (hexponent : 0 < exponent) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → C ≤ Z ^ exponent := by
  sorry

/-- Two original annuli and the quantitative pool deletion condition
are paid at one fixed scale, before any moving source is selected. -/
theorem exists_threshold :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      b.hi ^ (b.cap + 2) ≤ Z ^ b.loss ∧
      (b.lo ^ (b.cap + 2))⁻¹ ≤ Z ^ b.loss ∧
      2 * (b.rowBound / ((b.step / 3) / 2) +
        b.columnBound / ((b.step / 3) / 2)) ≤ Z ^ (b.step / 3 - b.loss) := by
  sorry

def threshold : ℝ := Classical.choose b.exists_threshold

theorem threshold_gt_one : 1 < b.threshold := by
  sorry

theorem threshold_windows (Z : ℝ) (hZ : b.threshold ≤ Z) :
    b.hi ^ (b.cap + 2) ≤ Z ^ b.loss ∧
      (b.lo ^ (b.cap + 2))⁻¹ ≤ Z ^ b.loss ∧
      2 * (b.rowBound / ((b.step / 3) / 2) +
        b.columnBound / ((b.step / 3) / 2)) ≤ Z ^ (b.step / 3 - b.loss) := by
  sorry

/-- The original scale and allocation thresholds are fixed together.
The extra power window also covers every retained or removed slot,
including an empty slot product. -/
theorem exists_fullThreshold :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ b.threshold ≤ Z₀ ∧ b.firstBox.threshold ≤ Z₀ ∧
      OriginalPairAllowanceProduction.annulusThreshold b.hi b.error ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        b.hi ^ (2 * b.cap) ≤ Z ^ b.error ∧ b.hi ≤ Z ^ (2 * b.loss) := by
  sorry

def fullThreshold : ℝ := Classical.choose b.exists_fullThreshold

theorem fullThreshold_spec :
    1 < b.fullThreshold ∧ b.threshold ≤ b.fullThreshold ∧
      b.firstBox.threshold ≤ b.fullThreshold ∧
      OriginalPairAllowanceProduction.annulusThreshold b.hi b.error ≤ b.fullThreshold ∧
      ∀ Z : ℝ, b.fullThreshold ≤ Z →
        b.hi ^ (2 * b.cap) ≤ Z ^ b.error ∧ b.hi ≤ Z ^ (2 * b.loss) := by
  sorry

end Box
end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.firstCutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.secondCutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.secondZero_loss
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.cap_mul_error_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.pooled_mass_loss
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.exists_threshold
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.exists_fullThreshold
