import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Data needed to state the two source transformations

Only small analytic parameters and the existing physical source records
occur here. In particular none of these records contains a parent
inequality, terminal estimate, normalized child or common-kernel bound.
The task contracts separately identify every source with the original
input and impose its explicit physical windows.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

/-- These parameters select only the two physical cutoffs and their
small logarithmic tilt. Tail orders, seminorms and constants are chosen
by separate uniform estimate tasks. -/
structure SourceParameters (c : TargetContext K) where
  loss : ℝ
  loss_pos : 0 < loss
  loss_small : 64 * loss ≤ recipeInductionSigma c
  loss_reserve : 4096 * ((c.geometry.slots : ℝ) + 1) * loss ≤
    sourceReserve c.family.lamA
  tilt : ℝ
  tilt_pos : 0 < tilt
  tilt_half : tilt ≤ 1 / 2
  tilt_le_loss : tilt ≤ loss
  firstCutoffExponent : ℝ
  firstCutoff_pos : 0 < firstCutoffExponent
  firstCutoff_small : firstCutoffExponent ≤ loss
  secondCutoffExponent : ℝ
  secondCutoff_pos : 0 < secondCutoffExponent
  secondCutoff_small : secondCutoffExponent ≤ loss

namespace SourceParameters

variable {c : TargetContext K} (p : SourceParameters c) (call : Call c)

def firstCutoff : ℝ := call.base ^ p.firstCutoffExponent
def secondCutoff : ℝ := call.base ^ p.secondCutoffExponent

theorem firstCutoff_one : 1 ≤ p.firstCutoff call :=
  Real.one_le_rpow call.domain.scale.le p.firstCutoff_pos.le

theorem secondCutoff_one : 1 ≤ p.secondCutoff call :=
  Real.one_le_rpow call.domain.scale.le p.secondCutoff_pos.le

end SourceParameters

/-- Concrete positive losses are fixed before all profile orders and
moving inputs. Both cutoffs retain a positive power, and the total
arithmetic loss fits the original reserve even at the slot cap. -/
def canonicalSourceParameters (c : TargetContext K) : SourceParameters c := by
  let denominator : ℝ := 4096 * ((c.geometry.slots : ℝ) + 1)
  have hd : 0 < denominator := by dsimp [denominator]; positivity
  have hs : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  have hr : 0 < sourceReserve c.family.lamA :=
    (moment_mesh_engine_bounds c.family.lamA_pos).2.1
  let loss : ℝ := min 1 (min (recipeInductionSigma c / 64)
    (sourceReserve c.family.lamA / denominator))
  have hloss : 0 < loss := by
    dsimp [loss]
    exact lt_min (by norm_num)
      (lt_min (div_pos hs (by norm_num)) (div_pos hr hd))
  have hscale : loss ≤ recipeInductionSigma c / 64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hreserve : loss ≤ sourceReserve c.family.lamA / denominator :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine {
    loss := loss
    loss_pos := hloss
    loss_small := by linarith
    loss_reserve := ?_
    tilt := min (1 / 4) loss
    tilt_pos := lt_min (by norm_num) hloss
    tilt_half := (min_le_left _ _).trans (by norm_num)
    tilt_le_loss := min_le_right _ _
    firstCutoffExponent := loss / 2
    firstCutoff_pos := div_pos hloss (by norm_num)
    firstCutoff_small := by linarith
    secondCutoffExponent := loss / 2
    secondCutoff_pos := div_pos hloss (by norm_num)
    secondCutoff_small := by linarith }
  simpa only [denominator, mul_comm] using (le_div_iff₀ hd).mp hreserve

namespace Call

variable {c : TargetContext K} (call : Call c)

/-- The complete old mask is charged at its actual norm. This keeps
the original width and the original two comparison lengths. -/
def oldSupport :=
  call.localizedSource.source.recipe.moving.effectiveFullSupport
    call.localizedSource.source.recipe.remaining

def supportLength : ℝ :=
  Real.log ((Arithmetic.data c).exteriorNorm call.oldSupport) / Real.log call.base

def workingParameters : RealParameters :=
  { call.node.parameters with
    m := call.node.parameters.m + call.node.parameters.q - call.supportLength
    q := call.supportLength }

def workingAtoms :=
  (call.localizedSource.source.recipe.arithmeticAtoms PUnit.unit).constantAtoms
    call.localizedNormProfiles call.workingParameters call.base 0

def workingRaw :=
  call.workingAtoms.raw (call.base ^ call.node.comparison₁)
    (call.base ^ call.node.comparison₂)

def workingValues :=
  call.workingAtoms.values (call.base ^ call.node.comparison₁)
    (call.base ^ call.node.comparison₂)

end Call

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance sourcePrincipal (c : TargetContext K) :
    IsPrincipalIdealRing (Arithmetic.data c).R := Arithmetic.principal c

local instance sourceNormOneSpace (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _

local instance sourceNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩

variable {c : TargetContext K}

abbrev FirstSource (call : Call c) (p : SourceParameters c) :=
  ActualDirectFirstSource (Γ := Arithmetic.unitSubgroup c) (E := ℝ)
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.context c) call.base
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    call.node.centered call.localizedData call.workingParameters 0
    (call.base ^ call.node.comparison₁) (call.base ^ call.node.comparison₂)
    (p.firstCutoff call) (p.firstCutoff_one call)

/-- The first common pair, physical mask divisor and residual
coprimality divisor are separate coordinates. The paid support must
not be replaced by the full deletion support in a later capacity task. -/
structure FirstCoordinates (call : Call c) where
  selected : HeckeGeneral.Analysis.NonzeroIdeal K
  opposite : HeckeGeneral.Analysis.NonzeroIdeal K
  complementary : HeckeGeneral.Analysis.NonzeroIdeal K
  residualDivisor : HeckeGeneral.Analysis.NonzeroIdeal K
  tag : OriginalNominalTag K
  retainedScale : ℝ
  retainedScale_pos : 0 < retainedScale
  fullDeletion : Finset (HeightOneSpectrum (𝓞 K))
  paidSupport : (Arithmetic.data c).Exterior

/-- One actual first-Cauchy summand, before the second transform.
The coefficient still contains its whole centered subtraction. -/
structure PhysicalSource (call : Call c) (p : SourceParameters c) where
  Column : Type
  source : ActualGaussSource (Arithmetic.context c) Column
  firstKernel : SchwartzMap ℝ ℂ
  firstPoint : Column → ℝ
  outerWeight : ℝ
  outerWeight_nonneg : 0 ≤ outerWeight
  first : FirstCoordinates call

/-- A second transform retains the identical physical Gauss source.
Its zero, nonzero and tail expressions are the base raw expressions. -/
structure SecondSource (call : Call c) (p : SourceParameters c) where
  physical : PhysicalSource call p
  stage : ActualGaussStage (Γ := Arithmetic.unitSubgroup c) (E := ℝ)
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.different c) physical.source
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
