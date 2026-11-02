import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformChoices
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinSourcePreparation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual original Schwartz representatives on each prepared call

The merged Mellin theorem constructs these representatives from the
selected parent's Euler-profile control. The two logarithmic source
passes use the same finite original order set and rank-local positive
annulus. Localizing the row predicate reuses all representatives.
A reference row is chosen only from an actual nonempty paired-row set.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.SelectedProfileData

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction HeckeSkeleton.Moments.EngineInduction.Source
open HeckeSkeleton.Moments.UniformAmplify EngineStep
open scoped Classical SchwartzMap

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

local instance selectedProfileReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance selectedProfileReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

variable (request : Request c frame Cp Hp hCp hminimum hHp)

def lower : ℝ := (selectedCall request).lower / 2
def upper : ℝ := 2 * (selectedCall request).upper
def window : Set ℝ := Set.Icc (lower request) (upper request)

theorem lower_pos : 0 < lower request :=
  div_pos (selectedCall request).lower_pos (by norm_num)

theorem window_positive : window request ⊆ Set.Ioi 0 :=
  fun _ hx => (lower_pos request).trans_le hx.1

theorem window_in_fixed : window request ⊆
    Set.Icc (profileRange c frame).expanded.lower (profileRange c frame).expanded.upper :=
  StrictProfileRange.expanded_contains_schedule frame.lower frame.upper frame.lower_pos
    frame.interval.le (rankCount c) (selectedRank request)

/-- This existing proved theorem supplies the actual Schwartz data.
The equality with the authoritative two-pass `originalOrders` is
`inputOrdersAtRank_eq`; no new existence proof is inserted here. -/
def parentRawWindow (frequency : ℝ × ℝ) :
    RawProfileWindow Set.univ Set.univ (window request)
      (inputOrdersAtRank c frame (selectedRank request))
      ((selectedCall request).model frequency).data
      (rawAmplitudeAtRank c frame (selectedRank request)) :=
  Classical.choice (mellinStrictModel_rawWindow (Ω := CombinedParameter)
    (profileRange c frame) (selectedVolumeOrders c frame)
    (childOrderAtRank c frame (selectedRank request))
    request.parent (selectedCall request).cap (selectedCall request).weight
    (selectedCall request).lower (selectedCall request).upper
    (selectedCall request).weight_nonneg (selectedCall request).lower_pos
    (selectedCall request).interval (window_in_fixed request)
    (selectedCall request).profileBudget (selectedCall request).profileBudget_one_le
    request.base (zero_lt_one.trans request.domain.scale)
    (selectedCall request).slot_cap (selectedCall request).profiles frequency)

/-- Only the allowed-row predicate is restricted. All four profile
representatives, bounds and support statements are reused verbatim. -/
def localizedRawWindow (frequency : ℝ × ℝ) :
    RawProfileWindow Set.univ Set.univ (window request)
      (inputOrdersAtRank c frame (selectedRank request))
      (localizeOriginalParent ((selectedCall request).model frequency).data
        ((selectedCall request).model frequency).parameters request.base)
      (rawAmplitudeAtRank c frame (selectedRank request)) :=
  localizedRawProfileWindow (parentRawWindow request frequency)
    ((selectedCall request).model frequency).parameters request.base

def rows (frequency : ℝ × ℝ) : Finset (NonzeroIdeal K) :=
  pairedRows ((selectedCall request).model frequency).data
    ((selectedCall request).model frequency).parameters request.base

def reference (frequency : ℝ × ℝ) (hrows : (rows request frequency).Nonempty) :
    NonzeroIdeal K := Classical.choose hrows

theorem reference_mem (frequency : ℝ × ℝ) (hrows : (rows request frequency).Nonempty) :
    reference request frequency hrows ∈ rows request frequency := Classical.choose_spec hrows

theorem reference_original_allowed (frequency : ℝ × ℝ)
    (hrows : (rows request frequency).Nonempty) :
    ((selectedCall request).model frequency).data.allowedRow (reference request frequency hrows) :=
  ((((selectedCall request).model frequency).data.rows_spec _ _).mp
    (Finset.mem_filter.mp (reference_mem request frequency hrows)).1).1

theorem reference_allowed (frequency : ℝ × ℝ) (hrows : (rows request frequency).Nonempty) :
    (localizeOriginalParent ((selectedCall request).model frequency).data
      ((selectedCall request).model frequency).parameters request.base).allowedRow
        (reference request frequency hrows) :=
  ⟨reference_original_allowed request frequency hrows, reference_mem request frequency hrows⟩

end HeckeSkeleton.Moments.EngineStepV2.SelectedProfileData
