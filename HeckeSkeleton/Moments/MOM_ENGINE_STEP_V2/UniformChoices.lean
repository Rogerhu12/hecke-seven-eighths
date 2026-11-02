import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PreparedCall
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PhysicalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.MassProfileChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourcePool

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform order, coefficient and profile choices

The choice order here is part of the public contract: the source frame
fixes the engine schedule and minimum source coefficient; Cp and Hp
then fix the common engine coefficient, height degree and scale
threshold; only afterward is a moving source request introduced.
Prepared calls contain original profile controls and scalar constants,
and do not contain the engine output being constructed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

local instance uniformReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance uniformReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

/-- Every genuine source contribution is paid by its own fixed scalar.
The first two entries cover both separate zero and tail terms. -/
def engineScalar (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  1 + 2 * firstScalar c frame + 2 * secondScalar c frame +
    exceptionalScalar c frame + massScalar c frame rank

theorem engineScalar_pos (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    0 < engineScalar c frame rank := by
  have h₁ := firstScalar_pos c frame
  have h₂ := secondScalar_pos c frame
  have h₃ := exceptionalScalar_pos c frame
  have h₄ := massScalar_pos c frame rank
  unfold engineScalar
  positivity

/-- The exact complete exceptional degree dominates the two-radius
mass degree; the comparison is a theorem, not an extra source premise. -/
def engineControlAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  rawAmplitudeAtRank c frame rank ^ exceptionalProfileDegree c.geometry.slots

theorem engineControlAtRank_one_le (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    1 ≤ engineControlAtRank c frame rank :=
  one_le_pow₀ (rawAmplitudeAtRank_one_le c frame rank)

theorem massProfileDegree_le_engine (cap : ℕ) :
    massProfileDegree cap ≤ exceptionalProfileDegree cap := by
  rw [massProfileDegree_eq, exceptionalProfileDegree_eq]
  omega

theorem massAmplitude_le_engineControl (c : TargetContext K) (frame : SourceFrame)
    (rank : ℕ) :
    rawAmplitudeAtRank c frame rank ^ massProfileDegree c.geometry.slots ≤
      engineControlAtRank c frame rank :=
  pow_le_pow_right₀ (rawAmplitudeAtRank_one_le c frame rank)
    (massProfileDegree_le_engine c.geometry.slots)

def rankCoefficient (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  mellinStrictMassConstant (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (Ω := CombinedParameter) c.geometry.slots (mellinOrderAtRank c frame rank)
    frame.decay (lowerAtRank c frame rank) (upperAtRank c frame rank)
    (zero_lt_one.trans frame.decay_gt_one).le
    (lowerAtRank_pos c frame rank) (annulusAtRank c frame rank) *
      (engineScalar c frame rank * engineControlAtRank c frame rank)

/-- An actual finite maximum, taken before the source height, scale,
index, node and all Fourier frequencies. -/
def maximumRankCoefficient (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  (Finset.range (rankCount c + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_pos (rankCount c)))
    (rankCoefficient c frame)

/-- All thresholds apply to the actual shell base. -/
def selectedBaseThreshold (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 2 (max (selectedBox c frame).fullThreshold
    (max (CanonicalPrimitiveEnginePool.threshold (TargetArithmetic.arithmetic c)
      (selectedBox c frame))
      (max (massScaleThreshold c frame) (exceptionalScaleThreshold c frame))))

theorem selectedBaseThreshold_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ selectedBaseThreshold c frame :=
  (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)

theorem selectedBaseThreshold_windows (c : TargetContext K) (frame : SourceFrame)
    {Z : ℝ} (hZ : selectedBaseThreshold c frame ≤ Z) :
    (selectedBox c frame).fullThreshold ≤ Z ∧
      CanonicalPrimitiveEnginePool.threshold (TargetArithmetic.arithmetic c)
        (selectedBox c frame) ≤ Z ∧
      massScaleThreshold c frame ≤ Z ∧ exceptionalScaleThreshold c frame ≤ Z := by
  obtain ⟨_, hb, hp, hm, he⟩ :=
    (show 2 ≤ Z ∧ (selectedBox c frame).fullThreshold ≤ Z ∧
      CanonicalPrimitiveEnginePool.threshold (TargetArithmetic.arithmetic c)
        (selectedBox c frame) ≤ Z ∧
      massScaleThreshold c frame ≤ Z ∧ exceptionalScaleThreshold c frame ≤ Z by
      simpa only [selectedBaseThreshold, max_le_iff] using hZ)
  exact ⟨hb, hp, hm, he⟩

/-- The shell exponent is at least `1/16`, so the physical source
threshold is the sixteenth power of the selected shell threshold. -/
def selectedBounds (c : TargetContext K) (frame : SourceFrame) (Cp Hp : ℝ)
    (hCp : 0 < Cp) (hminimum : (selectedSchedule c frame).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp) : UniformBounds where
  coefficient := max 1 (maximumRankCoefficient c frame) *
    (1 + Cp) ^ (2 * (c.geometry.slots + 2))
  heightDegree := Hp * ((2 * (c.geometry.slots + 2) : ℕ) : ℝ)
  threshold := selectedBaseThreshold c frame ^ (16 : ℕ)
  coefficient_nonneg := mul_nonneg (zero_le_one.trans (le_max_left _ _))
    (pow_nonneg (by linarith) _)
  heightDegree_nonneg := mul_nonneg hHp (Nat.cast_nonneg _)
  threshold_one_le := one_le_pow₀ (selectedBaseThreshold_one_le c frame)

/-- The same original request with its uniform choices already fixed. -/
abbrev Request (c : TargetContext K) (frame : SourceFrame) (Cp Hp : ℝ)
    (hCp : 0 < Cp) (hminimum : (selectedSchedule c frame).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp) :=
  SourceRequest c frame (selectedSchedule c frame) Cp Hp
    (selectedBounds c frame Cp Hp hCp hminimum hHp)

variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

def selectedRank (request : Request c frame Cp Hp hCp hminimum hHp) : ℕ :=
  parameterCoreRank (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    request.parent.parameters

theorem selectedRank_lt (request : Request c frame Cp Hp hCp hminimum hHp) :
    selectedRank request < rankCount c :=
  parameterCoreRank_lt_bound request.parent.parameters
    (recipeInduction_budget (c := c)).1 request.node.down.property.width_le

/-- A strict call is above the original positive width floor, so its
predecessor profile order is always an actual earlier schedule entry. -/
theorem selectedRank_pos (request : Request c frame Cp Hp hCp hminimum hHp) :
    0 < selectedRank request := by
  have hσ := (recipeInduction_budget (c := c)).1
  have hwidth : 16 * recipeInductionSigma c <
      request.parent.parameters.m + request.parent.parameters.q := request.domain.width_floor
  have hband : 0 < widthBand (recipeInductionSigma c)
      (request.parent.parameters.m + request.parent.parameters.q) := by
    have h := widthBand_strict hσ (le_refl (0 : ℝ))
      (show (0 : ℝ) + recipeInductionSigma c / 2 ≤
        request.parent.parameters.m + request.parent.parameters.q by linarith)
    simpa only [widthBand, mul_zero, zero_div, Nat.floor_zero] using h
  unfold selectedRank parameterCoreRank
  split_ifs <;> omega

theorem selectedBase_large (request : Request c frame Cp Hp hCp hminimum hHp) :
    selectedBaseThreshold c frame ≤ request.base :=
  _root_.ExpansionRecipe.shell_base_ge_of_physical_cutoff
    (selectedBaseThreshold_one_le c frame) request.large
    (recipeMoment_shell_lower request.index)

/-- This is the original node's existing scheduled Euler-profile
invariant weakened to the exact order required by Mellin preprocessing. -/
theorem selectedProfiles (request : Request c frame Cp Hp hCp hminimum hHp) :
    ModelProfileControl request.parent.data
      (mellinOrderAtRank c frame (selectedRank request) + 2) frame.decay
      (profileFamilyBudget Cp Hp request.height) 0
      (lowerAtRank c frame (selectedRank request))
      (upperAtRank c frame (selectedRank request)) 0 := by
  have hprofile : admissibleOfInvariant
      (rankedAnnulusProfilePrimitive 1 (selectedSchedule c frame).engine frame.reflection
        (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) frame.decay
        (profileFamilyBudget Cp Hp request.height) frame.lower frame.upper)
      request.parent.data request.parent.parameters :=
    request.node.down.property.admissible.2.2.2.2
  rw [rankedAnnulusProfilePrimitive_iff] at hprofile
  exact modelProfileControl_mono_order hprofile
    (backwardProfileOrder_parent_orders 1 (selectedSchedule c frame).engine
      frame.reflection (selectedRank_pos request)).1

/-- The literal node's scheduled Euler profiles choose the actual
Mellin order and positive annulus before any Fourier frequency. -/
def selectedCall (request : Request c frame Cp Hp hCp hminimum hHp) :
    PreparedCall request.parent where
  cap := c.geometry.slots
  order := mellinOrderAtRank c frame (selectedRank request)
  weight := frame.decay
  lower := lowerAtRank c frame (selectedRank request)
  upper := upperAtRank c frame (selectedRank request)
  weight_nonneg := (zero_lt_one.trans frame.decay_gt_one).le
  lower_pos := lowerAtRank_pos c frame (selectedRank request)
  interval := annulusAtRank c frame (selectedRank request)
  profileBudget := profileFamilyBudget Cp Hp request.height
  profileBudget_one_le := profileFamilyBudget_one_le hCp.le hHp request.height_nonneg
  slot_cap := request.node.down.property.slot_count
  profiles := selectedProfiles request
  engineCoefficient := engineScalar c frame (selectedRank request)
  engineControl := engineControlAtRank c frame (selectedRank request)
  engineCoefficient_nonneg := (engineScalar_pos c frame (selectedRank request)).le
  engineControl_nonneg := zero_le_one.trans
    (engineControlAtRank_one_le c frame (selectedRank request))

/-- This pays only the outer Mellin scalar and the chosen common
engine coefficient. No source or child moment estimate is assumed. -/
theorem selectedCall_budget (request : Request c frame Cp Hp hCp hminimum hHp) :
    (selectedCall request).mellinCost ≤
      (selectedBounds c frame Cp Hp hCp hminimum hHp).coefficient *
        (1 + request.height) ^
          (selectedBounds c frame Cp Hp hCp hminimum hHp).heightDegree := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2

