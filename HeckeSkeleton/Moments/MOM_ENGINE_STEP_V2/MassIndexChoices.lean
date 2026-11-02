import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.AnalyticChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoordinateSubpower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# Fixed costs of the actual arithmetic and passive labels

The two passive divisor labels contribute the square of the actual
divisor/allocation bound, with the four rectangle choices. The physical
mask and coordinate constants are the original proved counting choices.
The direct and amplified harmonic constants retain the same two-divisor
index and the one/six/seven tags. No constructed family estimate is chosen.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineStep HeckeSkeleton.Moments.EngineInduction
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K]

namespace MassIndexChoices

local instance massIndexUnitClassesFintype (c : TargetContext K) :
    Fintype (SixthUnitClasses K
      ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.ofFinite _

/-- The explicit witness in the passive-pair cardinality argument.
Half the loss is assigned to each side, and then equally to divisors
and allocations. The norm window is paid before the moving ideal. -/
def passivePairConstant (cap : ℕ) (box ε : ℝ) (hbox : 0 ≤ box) (hε : 0 < ε) : ℝ :=
  let δ := (ε / 2) / (box + 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  4 * ((ideal_divisor_count_le_rpow K δ hδ).choose *
    (AllocationMass.ideal_allocation_card_bound K (cap + 2) δ hδ).choose) ^ 2

theorem passivePairConstant_pos (cap : ℕ) (box ε : ℝ)
    (hbox : 0 ≤ box) (hε : 0 < ε) :
    0 < passivePairConstant (K := K) cap box ε hbox hε := by
  sorry

def firstMaskConstant (box ε : ℝ) (hbox : 0 ≤ box) (hε : 0 < ε) : ℝ :=
  (first_block_mask_labels_subpower.{0, 0} (K := K) box ε hbox hε).choose

def physicalConstant (c : TargetContext K) (cap : ℕ) (box ε : ℝ)
    (hbox : 0 ≤ box) (hε : 0 < ε) : ℝ :=
  2 * firstMaskConstant (K := K) box (ε / 8) hbox (by positivity) *
    OriginalFiniteFibre.coordinateConstant (K := K) cap
      (Fintype.card (PUnit.{1} × SixthUnitClasses K
        ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))))
      0 0 box (ε / 8) hbox (by positivity)

variable (c : TargetContext K) (frame : SourceFrame)

local notation "b" => selectedBox c frame
local notation "loss" => massLoss c frame

def directPassive : ℝ :=
  passivePairConstant (K := K) b.cap b.columnBound (loss / 8)
    b.columnBound_nonneg (by have h := massLoss_pos c frame; positivity)

def pooledPassive : ℝ :=
  max (directPassive c frame)
    (passivePairConstant (K := K) b.cap (b.columnBound + 2 * (b.step / 3)) (loss / 8)
      (by have h₁ := b.columnBound_nonneg; have h₂ := b.step_pos; positivity)
      (by have h := massLoss_pos c frame; positivity))

def directPhysical : ℝ :=
  physicalConstant c b.cap b.columnBound (loss / 2) b.columnBound_nonneg
    (half_pos (massLoss_pos c frame))

def pooledPhysical : ℝ :=
  physicalConstant c b.cap (b.columnBound + 7 * (b.step / 3)) (loss / 2)
    (by have h₁ := b.columnBound_nonneg; have h₂ := b.step_pos; positivity)
    (half_pos (massLoss_pos c frame))

def directHarmonic : ℝ :=
  (TwoDivisorCommonBranch.uniform_index_mass (K := K)
    (b.cap + 2) b.columnBound loss b.columnBound_nonneg (massLoss_pos c frame)).choose

theorem poolLoss_small : b.loss < b.step / 3 := by
  have h := b.loss_le_step
  have hs := b.step_pos
  linarith

/-- The original second-fibre count uses the actual original row exponent. -/
def pooledFibreCap : ℕ :=
  max 1 ⌈(b.rowBound + 6 * (b.step / 3)) / ((b.step / 3) / 2)⌉₊

private def harmonicExistence :=
  amplified_finite_index_mass (A := TargetArithmetic.arithmetic c)
    (b.cap + 2) b.columnBound loss (b.step / 3) b.loss b.rowBound b.columnBound
    b.columnBound_nonneg (massLoss_pos c frame)
    (div_pos b.step_pos (by norm_num)) b.loss_pos (poolLoss_small c frame)
    b.rowBound_nonneg b.columnBound_nonneg

def pooledHarmonic : ℝ := (harmonicExistence c frame).choose

def pooledThreshold : ℝ := (harmonicExistence c frame).choose_spec.choose

theorem pooledThreshold_gt_one : 1 < pooledThreshold c frame :=
  (harmonicExistence c frame).choose_spec.choose_spec.2.1

theorem directHarmonic_pos : 0 < directHarmonic c frame :=
  (TwoDivisorCommonBranch.uniform_index_mass (K := K)
    (b.cap + 2) b.columnBound loss b.columnBound_nonneg (massLoss_pos c frame)).choose_spec.1

theorem pooledHarmonic_pos : 0 < pooledHarmonic c frame :=
  (harmonicExistence c frame).choose_spec.choose_spec.1

end MassIndexChoices

def massScaleThreshold (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  MassIndexChoices.pooledThreshold c frame

theorem massScaleThreshold_gt_one (c : TargetContext K) (frame : SourceFrame) :
    1 < massScaleThreshold c frame := MassIndexChoices.pooledThreshold_gt_one c frame

end HeckeSkeleton.Moments.EngineStepV2
