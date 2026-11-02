import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PhysicalConstants
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.MassIndexChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedExceptionalMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The explicit exceptional scalar and its original index threshold

The volume coefficients were selected before the backward profile
schedule. Their two original Fourier factors and all original label
costs are now multiplied explicitly. The direct and pooled dyad
constants are selected from the proved base counting theorems. No
exceptional leaf, terminal certificate or completed sum is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineStep.CommonSupportMass
open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

namespace ExceptionalChoices

variable (c : TargetContext K) (frame : SourceFrame)

local notation "b" => selectedBox c frame
local notation "J" => VolumeChoices.heightOrder c b

local instance exceptionalChoiceUnitClassesFintype :
    Fintype (SixthUnitClasses K
      ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.ofFinite _

def profileCoefficient : ℝ :=
  1 + CanonicalLogProfiles.shapeCoefficient (Set.Icc (b).lo (b).hi) isCompact_Icc
    (VolumeChoices.positive b)
    (-1 + (b).tilt + (b).tilt) (CanonicalLogProfiles.sourceOrders (VolumeChoices.orders c b))

/-- The original two atom budgets include the central annulus payment. -/
def pairCoefficient : ℝ :=
  (b).hi ^ (2 * (b).cap) *
    (idealCountConstant K ^ (2 * (b).cap) * (b).hi ^ (5 * (b).cap + 2))

def firstCoefficient : ℝ := orbitalFieldFactor K * (b).hi ^ (b).cap

def sourceCoefficient : ℝ :=
  (b).hi ^ (b).cap * orbitalFieldFactor K *
    ((sixthPowerSUnitSubgroup K
      ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))).index : ℝ) *
    (pairCoefficient c frame * profileCoefficient c frame ^ (10 * (b).cap + 8) *
      VolumeChoices.constant c b)

def fourierFactor : ℝ :=
  let F := exceptionalFourierControl (U := ℝ) (E := ℝ) J J
  F.constant * F.leftSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (rawTerminalData c b).kernel *
    F.rightSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (rawTerminalData c b).kernel

def integralCoefficient : ℝ :=
  ((Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)).card : ℝ) ^ 2 *
    firstCoefficient c frame * sourceCoefficient c frame *
      (1 + 2 * Real.pi) ^ J * fourierFactor c frame

def leafCoefficient : ℝ :=
  (PhysicalConstants.poolFiberCap b : ℝ) * integralCoefficient c frame

def indexLoss : ℝ := (b).ε / 64

theorem indexLoss_pos : 0 < indexLoss c frame := div_pos (b).ε_pos (by norm_num)

def indexBox : ℝ := (b).columnBound + 7 * ((b).step / 3)

theorem indexBox_nonneg : 0 ≤ indexBox c frame := by
  have hB := (b).columnBound_nonneg
  have hs := (b).step_pos
  unfold indexBox
  positivity

/-- These are the mask and actual finite-coordinate factors in the
literal source-to-arithmetic-carrier map, including its two entrances. -/
def physicalCoefficient (box : ℝ) (hbox : 0 ≤ box) : ℝ :=
  2 * MassIndexChoices.firstMaskConstant (K := K) box (indexLoss c frame)
      hbox (indexLoss_pos c frame) *
    OriginalFiniteFibre.coordinateConstant (K := K) (b).cap
      (Fintype.card (PUnit.{1} × SixthUnitClasses K
        ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))))
      0 0 box (indexLoss c frame) hbox (indexLoss_pos c frame)

def directHarmonic : ℝ :=
  (TwoDivisorCommonBranch.uniform_exceptional_dyad_mass (K := K)
    ((b).cap + 2) (b).columnBound (indexLoss c frame)
    (b).columnBound_nonneg (indexLoss_pos c frame)).choose

private def pooledExistence :=
  uniform_amplified_exceptional_dyad_mass (A := TargetArithmetic.arithmetic c)
    ((b).cap + 2) (indexBox c frame) (indexLoss c frame)
    ((b).step / 3) (b).loss (b).rowBound (b).columnBound
    (indexBox_nonneg c frame) (indexLoss_pos c frame)
    (div_pos (b).step_pos (by norm_num)) (b).loss_pos (MassIndexChoices.poolLoss_small c frame)
    (b).rowBound_nonneg (b).columnBound_nonneg

def pooledHarmonic : ℝ := (pooledExistence c frame).choose
def pooledThreshold : ℝ := (pooledExistence c frame).choose_spec.choose

def directConstant : ℝ :=
  (leafCoefficient c frame + 1) *
    (physicalCoefficient c frame (b).columnBound (b).columnBound_nonneg * directHarmonic c frame)

def pooledConstant : ℝ :=
  (leafCoefficient c frame + 1) *
    (physicalCoefficient c frame (indexBox c frame) (indexBox_nonneg c frame) *
      pooledHarmonic c frame)

theorem directConstant_pos : 0 < directConstant c frame := by
  sorry

theorem pooledConstant_pos : 0 < pooledConstant c frame := by
  sorry

theorem pooledThreshold_gt_one : 1 < pooledThreshold c frame :=
  (pooledExistence c frame).choose_spec.choose_spec.2.1

end ExceptionalChoices

def exceptionalScalar (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  1 + ExceptionalChoices.directConstant c frame + ExceptionalChoices.pooledConstant c frame

theorem exceptionalScalar_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < exceptionalScalar c frame := by
  have hd := ExceptionalChoices.directConstant_pos c frame
  have hp := ExceptionalChoices.pooledConstant_pos c frame
  unfold exceptionalScalar
  linarith

def exceptionalScaleThreshold (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max (selectedBox c frame).fullThreshold
    (max (max 2 (Ideal.absNorm (TargetArithmetic.arithmetic c).cS : ℝ))
      (ExceptionalChoices.pooledThreshold c frame))

/-- Two original first scalar factors, the complete pair atom budget,
four plain volume profiles and the common frozen profile. -/
def exceptionalProfileDegree (cap : ℕ) : ℕ :=
  2 * cap + ((10 * cap + 4 + 4) + (2 * cap + 2))

theorem exceptionalProfileDegree_eq (cap : ℕ) :
    exceptionalProfileDegree cap = 14 * cap + 10 := by
  unfold exceptionalProfileDegree
  omega

end HeckeSkeleton.Moments.EngineStepV2
