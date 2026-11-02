import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaContracts
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TargetPrimeAnalyticInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaPrime

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: original analytic constants chosen before every moving source

The norm box is two, the original induction width bound. The length
bound is the fixed original slot mesh. The contour pays the complete
number of profiles before any slot removal, on both sides. These choices
depend on the target and the requested loss, never on a source, a
Fourier variable, a normalized child or a kernel estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.N6

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

/-- The target's existing boundary supplies the original analytic
window. The merged numerical theorem then chooses one contour for the
full pre-removal profile power, before all source data. -/
theorem exists_analyticChoices (c : TargetContext K) (loss : ℝ) (hloss : 0 < loss) :
    Nonempty (FullKappaChoices c loss) := by
  obtain ⟨heightC, hheightC, window⟩ :=
    actualSourcePrimeAnalyticProvider c (momentRowCharacters K c) 2 (by norm_num)
  obtain ⟨contour, radiusConstant, hcontour, hquarter, hconstant, hbound⟩ :=
    CanonicalFullKappaPrime.exists_complete_profile_radius_bound
      (Arithmetic.data c) (fullKappaProfilePower c) 0 loss (fullKappaLengthBound c)
      (CanonicalHeckePrimeAnalytic.degreeBound K) heightC 2 hloss
      CanonicalHeckePrimeAnalytic.degreeBound_pos.le (by norm_num)
  refine ⟨{
    heightC := heightC
    heightC_pos := hheightC
    window := window
    contour := contour
    contour_pos := hcontour
    contour_le_quarter := hquarter
    radiusConstant := radiusConstant
    radiusConstant_one_le := hconstant
    radius_power := ?_ }⟩
  intro Z hZ
  have h := hbound Z 0 2 (heightC * (1 + Real.log Z)) hZ (by norm_num)
    le_rfl (by simp)
  simpa only [add_zero, one_pow, mul_one] using h

/-- Select only the fixed original analytic and numerical choices. -/
def analyticChoices (c : TargetContext K) (loss : ℝ) (hloss : 0 < loss) :
    FullKappaChoices c loss :=
  Classical.choice (exists_analyticChoices c loss hloss)

end HeckeSkeleton.Moments.EngineStepV2.N6

#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.analyticChoices
