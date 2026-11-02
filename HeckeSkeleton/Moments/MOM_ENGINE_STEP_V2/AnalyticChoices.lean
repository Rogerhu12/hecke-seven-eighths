import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TargetArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TargetPrimeAnalyticInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaPrime

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original analytic height and the full pre-removal contour

The height is the explicit scalar in the proved original moving-character
provider. Its sole choice is the existing uniform Hecke strip constant.
The contour and radius constant are then chosen from the existing single
profile theorem, before any scale, recipe, normalized leaf or kernel.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.ActualEulerLogarithm
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open HeckeSkeleton.PrimeCancellationBounds EngineStep
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K]

def analyticStripConstant (c : TargetContext K) : ℝ :=
  (exists_uniform_finiteOrder_polynomial K (isComplex_of_family K c)).choose

def analyticConductorConstant (c : TargetContext K) : ℝ :=
  primeThetaConductorConstant
    ((TargetArithmetic.arithmetic c).Sf : Set (HeightOneSpectrum (𝓞 K)))
    (MovingRecipe.primeBackgrounds
      (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)))

/-- This is the actual provider's formula, independent of its row input. -/
def analyticHeightConstant (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  1 + Real.log (analyticStripConstant c) + (5 / 8 : ℝ) *
    (1 + Real.log (analyticConductorConstant c) + (selectedBox c frame).rawNormBound) +
      eulerLogSize K + 3 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)

theorem analyticHeightConstant_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < analyticHeightConstant c frame := by
  sorry

theorem analyticHeightWindow (c : TargetContext K) (frame : SourceFrame)
    (rows : RowCharacterInput K (places K c) (probeData K c)) :
    CanonicalOriginalPrimeAnalyticProvider.Window
      (A := TargetArithmetic.arithmetic c) (P := probeData K c) (R := rows)
      (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c))
      (selectedBox c frame).rawNormBound (analyticHeightConstant c frame) := by
  sorry

def massLoss (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  (selectedBox c frame).ε / 16

theorem massLoss_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < massLoss c frame :=
  div_pos (selectedBox c frame).ε_pos (by norm_num)

/-- All plain profiles and every original slot are charged on both sides. -/
def massRadiusPower (c : TargetContext K) : ℕ :=
  (c.geometry.slots + 2) + (c.geometry.slots + 2)

def analyticContour (c : TargetContext K) (frame : SourceFrame) (_rank : ℕ) : ℝ :=
  (CanonicalFullKappaPrime.exists_complete_profile_radius_bound
    (TargetArithmetic.arithmetic c) (massRadiusPower c) 0
    (massLoss c frame / 2) (momentMesh K c.family).val
    (CanonicalHeckePrimeAnalytic.degreeBound K) (analyticHeightConstant c frame)
    (selectedBox c frame).rawNormBound
    (half_pos (massLoss_pos c frame)) CanonicalHeckePrimeAnalytic.degreeBound_pos.le
    (selectedBox c frame).rawNormBound_nonneg).choose

def analyticRadiusConstant (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  (CanonicalFullKappaPrime.exists_complete_profile_radius_bound
    (TargetArithmetic.arithmetic c) (massRadiusPower c) 0
    (massLoss c frame / 2) (momentMesh K c.family).val
    (CanonicalHeckePrimeAnalytic.degreeBound K) (analyticHeightConstant c frame)
    (selectedBox c frame).rawNormBound
    (half_pos (massLoss_pos c frame)) CanonicalHeckePrimeAnalytic.degreeBound_pos.le
    (selectedBox c frame).rawNormBound_nonneg).choose_spec.choose

theorem analyticContour_pos (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    0 < analyticContour c frame rank := by
  sorry

theorem analyticContour_le_quarter (c : TargetContext K) (frame : SourceFrame) (rank : ℕ) :
    analyticContour c frame rank ≤ 1 / 4 := by
  sorry

theorem analyticRadiusConstant_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ analyticRadiusConstant c frame := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2
