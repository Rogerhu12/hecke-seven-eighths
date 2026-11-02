import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.VolumeChoices
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StrictProfileOrder

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Finite profile orders and the fixed physical box

The supported volume order union is fixed before the backward order
schedule. The same merged Schwartz/Euler bridges select both the
Mellin order and raw amplitude. Numerical estimates use one maximal
annulus; actual profiles keep their narrower rank-dependent supports.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

def rankCount (c : TargetContext K) : ℕ := 6 * (widthBand (recipeInductionSigma c) 2 + 1)

def profileRange (c : TargetContext K) (frame : SourceFrame) : StrictProfileRange :=
  StrictProfileRange.ofSchedule frame.lower frame.upper frame.lower_pos
    frame.interval.le (rankCount c)

/-- The actual physical choices are common to all finite ranks. The
upper annulus also covers the inverse lower endpoint used by the
exceptional ideal estimate. This does not enlarge actual child support. -/
def selectedBox (c : TargetContext K) (frame : SourceFrame) :
    CanonicalPrimitiveEngineChoices.Box where
  cap := c.geometry.slots
  widthMax := 2
  paddingMax := recipeInductionSigma c / 16
  lo := (profileRange c frame).expanded.lower
  hi := max (profileRange c frame).expanded.upper (profileRange c frame).expanded.lower⁻¹
  step := recipeInductionSigma c
  ε := sourceReserve c.family.lamA
  width_nonneg := by norm_num
  padding_nonneg := div_nonneg (recipeInduction_budget (c := c)).1.le (by norm_num)
  lo_pos := (profileRange c frame).expanded.lower_pos
  lo_le_one := by
    sorry
  hi_ge_one := by
    sorry
  step_pos := (recipeInduction_budget (c := c)).1
  ε_pos := by
    sorry

def selectedVolumeOrders (c : TargetContext K) (frame : SourceFrame) : Finset (ℕ × ℕ) :=
  VolumeChoices.orders c (selectedBox c frame)

def selectedEngineOrder (c : TargetContext K) (frame : SourceFrame) : ℕ → ℕ :=
  (profileRange c frame).engineOrder
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (selectedVolumeOrders c frame) frame.decay

/-- Every datum is computed by the existing finite profile choosers;
no engine output or new existence premise is used to select this data. -/
def selectedSchedule (c : TargetContext K) (frame : SourceFrame) : OrderSchedule where
  engine := selectedEngineOrder c frame
  minimumCp := strictChildProfileMinimum
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    1 (selectedEngineOrder c frame) frame.reflection (recipeInductionSigma c)
    2 (recipeInductionSigma c / 16) frame.decay frame.lower frame.upper
    frame.lower_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) frame.upper_large)

theorem selectedSchedule_minimumCp_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ (selectedSchedule c frame).minimumCp :=
  strictChildProfileMinimum_one_le 1 (selectedEngineOrder c frame) frame.reflection
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    frame.decay frame.lower frame.upper frame.lower_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) frame.upper_large)

def childOrderAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℕ :=
  backwardProfileOrder 1 (selectedSchedule c frame).engine frame.reflection (rank - 1)

def mellinOrderAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℕ :=
  (profileRange c frame).mellinOrder
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (selectedVolumeOrders c frame) (childOrderAtRank c frame rank) frame.decay

def outputOrdersAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    Finset (ℕ × ℕ) :=
  eulerSchwartzOrders (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (profileRange c frame).lower (profileRange c frame).upper
    (profileRange c frame).lower_pos (childOrderAtRank c frame rank) frame.decay

def childOrdersAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    Finset (ℕ × ℕ) :=
  (profileRange c frame).childOrders
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (selectedVolumeOrders c frame) (childOrderAtRank c frame rank) frame.decay

def inputOrdersAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    Finset (ℕ × ℕ) :=
  (profileRange c frame).inputOrders
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (selectedVolumeOrders c frame) (childOrderAtRank c frame rank) frame.decay

def rawAmplitudeAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  (profileRange c frame).amplitude
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (selectedVolumeOrders c frame) (childOrderAtRank c frame rank) frame.decay

theorem rawAmplitudeAtRank_one_le (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    1 ≤ rawAmplitudeAtRank c frame rank :=
  (profileRange c frame).amplitude_one_le
    (selectedVolumeOrders c frame) (childOrderAtRank c frame rank) frame.decay

def lowerAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  clippedAnnulusLower frame.lower frame.upper (rankCount c) rank

def upperAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) : ℝ :=
  rankedAnnulusUpper frame.upper (rankCount c) rank

theorem lowerAtRank_pos (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    0 < lowerAtRank c frame rank :=
  (clippedAnnulus_bounds frame.lower_pos frame.interval.le (rankCount c) rank).1

theorem annulusAtRank (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    lowerAtRank c frame rank ≤ upperAtRank c frame rank :=
  (clippedAnnulus_bounds frame.lower_pos frame.interval.le (rankCount c) rank).2

end HeckeSkeleton.Moments.EngineStepV2
