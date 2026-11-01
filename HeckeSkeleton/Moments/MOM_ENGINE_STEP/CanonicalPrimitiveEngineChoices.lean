import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalParentFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveTerminalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalEngineSmallParameters

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

def loss : ℝ := boundary b.step b.ε

def tilt : ℝ := CanonicalEngineSmallParameters.tilt b.normBound b.ε

def saving : ℝ := tailSaving b.normBound

theorem lengthBound_nonneg : 0 ≤ b.lengthBound :=
  add_nonneg b.width_nonneg b.padding_nonneg

theorem columnBound_nonneg : 0 ≤ b.columnBound := by
  have h := b.lengthBound_nonneg
  unfold columnBound
  linarith

theorem normBound_nonneg : 0 ≤ b.normBound :=
  b.lengthBound_nonneg.trans (le_max_left _ _)

theorem loss_pos : 0 < b.loss := boundary_pos b.step_pos b.ε_pos

theorem loss_le_one : b.loss ≤ 1 := boundary_le_one b.step b.ε

theorem loss_le_step : b.loss ≤ b.step / 64 := boundary_le_step b.step b.ε

theorem loss_le_ε : b.loss ≤ b.ε / 4096 := boundary_le_loss b.step b.ε

theorem tilt_pos : 0 < b.tilt := (tilt_properties b.normBound_nonneg b.ε_pos).1

theorem tilt_le_quarter : b.tilt ≤ 1 / 4 :=
  (tilt_properties b.normBound_nonneg b.ε_pos).2.1

theorem tilt_le_half : b.tilt ≤ 1 / 2 := by
  linarith [b.tilt_le_quarter]

theorem saving_pos : 0 < b.saving := (tailSaving_properties b.normBound_nonneg).1

theorem saving_ge_column : 2 * b.columnBound ≤ b.saving :=
  (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (tailSaving_properties b.normBound_nonneg).2

def firstDegree : ℝ := originalFirstPhysicalDegree b.cap b.columnBound

def secondDegree : ℝ := CanonicalOriginalTerminalPowers.primitiveDegree
  b.cap b.lengthBound b.columnBound b.step b.loss b.loss

def firstDecay : ℝ := tailDecayForWidth b.firstDegree b.saving b.loss

def secondDecay : ℝ := tailDecayForWidth b.secondDegree b.saving b.loss

theorem firstDecay_gt_one : 1 < b.firstDecay :=
  tailDecayForWidth_gt_one b.firstDegree b.saving b.loss b.loss_pos

theorem secondDecay_gt_one : 1 < b.secondDecay :=
  tailDecayForWidth_gt_one b.secondDegree b.saving b.loss b.loss_pos

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

theorem firstCutoffExponent_le : b.firstBox.cutoffExponent ≤ b.loss :=
  firstTailCutoffExponent_le_width b.firstDegree b.saving b.loss
    b.firstDegree b.loss_pos le_rfl

theorem firstCutoff_le (Z : ℝ) (hZ : 1 ≤ Z) : b.firstBox.cutoff Z ≤ Z ^ b.loss :=
  Real.rpow_le_rpow_of_exponent_le hZ b.firstCutoffExponent_le

/-- The second cutoff keeps the full original main and error degree. -/
def secondCutoff (Z : ℝ) : ℝ :=
  CanonicalOriginalTerminalPowers.primitiveCutoff b.cap b.lengthBound b.columnBound
    b.step b.loss b.loss b.saving b.secondDecay Z

theorem secondCutoff_ge_one (Z : ℝ) (hZ : 1 ≤ Z) : 1 ≤ b.secondCutoff Z :=
  CanonicalOriginalTerminalPowers.primitiveCutoff_ge_one b.cap b.lengthBound b.columnBound
    b.step b.loss b.loss b.saving b.secondDecay Z hZ b.secondDecay_gt_one

theorem secondCutoff_le (Z : ℝ) (hZ : 1 ≤ Z) : b.secondCutoff Z ≤ Z ^ b.loss := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  exact firstTailCutoffExponent_le_width b.secondDegree b.saving b.loss
    b.secondDegree b.loss_pos le_rfl

theorem width_margin : 2 * (2 * b.loss + b.loss) ≤ b.step := by
  have h := b.loss_le_step
  linarith

theorem pool_separation : b.loss < b.step / 6 ∧ b.loss < b.step / 3 :=
  (boundary_pool_separation b.step_pos b.ε_pos).2

/-- All raw second-zero small powers fit in the same requested loss;
the principal padding and step remain visible to the induction. -/
theorem secondZero_loss :
    (2 * b.loss + b.loss) + 2 * b.loss +
      (4 * b.normBound + 2) * b.tilt +
      2 * (b.normBound + 1) * b.tilt + b.loss + b.ε / 8 ≤ b.ε / 4 := by
  have h := second_zero_small_budget b.step_pos b.ε_pos b.normBound_nonneg
  simpa only [supportError, loss, tilt, show (3 : ℝ) = 2 + 1 by norm_num, add_mul, one_mul]
    using h

/-- The same coarse row box is used on both first Gauss sides. -/
def rowBound : ℝ := 2 * b.lengthBound + 2 * b.columnBound + 2 * b.loss + b.loss

theorem rowBound_nonneg : 0 ≤ b.rowBound := by
  have h₁ := b.lengthBound_nonneg
  have h₂ := b.columnBound_nonneg
  have h₃ := b.loss_pos.le
  unfold rowBound
  positivity

private theorem exists_power_threshold (C exponent : ℝ) (hexponent : 0 < exponent) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → C ≤ Z ^ exponent := by
  have hevent := (_root_.tendsto_rpow_atTop hexponent).eventually
    (Filter.eventually_ge_atTop C)
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun Z hZ => hZ₁ Z ((le_max_left _ _).trans hZ)⟩

/-- Two original annuli and the quantitative pool deletion condition
are paid at one fixed scale, before any moving source is selected. -/
theorem exists_threshold :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      b.hi ^ (b.cap + 2) ≤ Z ^ b.loss ∧
      (b.lo ^ (b.cap + 2))⁻¹ ≤ Z ^ b.loss ∧
      2 * (b.rowBound / ((b.step / 3) / 2) +
        b.columnBound / ((b.step / 3) / 2)) ≤ Z ^ (b.step / 3 - b.loss) := by
  obtain ⟨Z₁, hZ₁, h₁⟩ := exists_power_threshold
    (max (b.hi ^ (b.cap + 2)) ((b.lo ^ (b.cap + 2))⁻¹)) b.loss b.loss_pos
  obtain ⟨Z₂, hZ₂, h₂⟩ := exists_power_threshold
    (2 * (b.rowBound / ((b.step / 3) / 2) + b.columnBound / ((b.step / 3) / 2)))
    (b.step / 3 - b.loss) (sub_pos.mpr b.pool_separation.2)
  refine ⟨max Z₁ Z₂, hZ₁.trans_le (le_max_left _ _), ?_⟩
  intro Z hZ
  have hann := h₁ Z ((le_max_left _ _).trans hZ)
  exact ⟨(le_max_left _ _).trans hann, (le_max_right _ _).trans hann,
    h₂ Z ((le_max_right _ _).trans hZ)⟩

def threshold : ℝ := Classical.choose b.exists_threshold

theorem threshold_gt_one : 1 < b.threshold := (Classical.choose_spec b.exists_threshold).1

theorem threshold_windows (Z : ℝ) (hZ : b.threshold ≤ Z) :
    b.hi ^ (b.cap + 2) ≤ Z ^ b.loss ∧
      (b.lo ^ (b.cap + 2))⁻¹ ≤ Z ^ b.loss ∧
      2 * (b.rowBound / ((b.step / 3) / 2) +
        b.columnBound / ((b.step / 3) / 2)) ≤ Z ^ (b.step / 3 - b.loss) :=
  (Classical.choose_spec b.exists_threshold).2 Z hZ

end Box
end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.firstCutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.secondCutoff_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.secondZero_loss
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineChoices.Box.exists_threshold
