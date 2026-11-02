import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalCapacityContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N8b candidate: the mass of the same canonical refined family

The inputs are precisely the single-source constructions of N1--N6.
The source, normalizer, calibration, geometry and normalized capacity
are all fixed to those constructions.  In particular the result does
not quantify over a freely supplied normalized family.

The arithmetic index loss is fixed to p.loss.  N8a can be instantiated
at this positive loss, leaving its exponent 2 * p.loss to cancel here.
Every cost and threshold precedes the moving call and all its labels.
Paper: lines 2908--2946, including the actual whole-slot removal loss.

The shared imports retain the original upstream declaration names.
This candidate follows the final contract frozen by B; its source
closure is compiled and recursively audited by the task CI.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- Consumption view of earlier constructions.  All fields fix actual
source atoms or individual original windows. No child-weight bound,
arithmetic mass estimate or finite-fibre estimate is supplied. -/
structure CanonicalMassPacket (packet : RawLeafPacket call p)
    (input : ProfileInput call) (choices : FullKappaChoices c p.loss) where
  seed : OrdinarySeed packet
  support : seed.ordinary.PassiveSupport input
  support_actual : seed.CanonicalSupport input support
  residual_mask : seed.ResidualMaskIdentity
  calibrations : (seed.refinement input support).Calibrations
  calibration_actual : ∀ side a rectangle,
    OriginalCalibrationSpec seed input support side a rectangle
      (calibrations.side side a rectangle)
  geometry : OriginalCapacityCertificate seed support calibrations
  coefficient : ∀ side, support.labels side → Bool → ℝ
  firstDegree : ∀ side, support.labels side → Bool → ℕ
  secondDegree : ∀ side, support.labels side → Bool → ℕ
  windows : ∀ side a rectangle,
    FullKappaWindows (calibrations.side side a rectangle)
      (coefficient side a rectangle) (firstDegree side a rectangle)
      (secondDegree side a rectangle)
  normalization : ∀ side a rectangle,
    FullKappaSideResult choices (geometry.geometry side a rectangle)
      (windows side a rectangle)

namespace CanonicalMassPacket

variable {packet : RawLeafPacket call p} {input : ProfileInput call}
variable {choices : FullKappaChoices c p.loss}
variable (P : CanonicalMassPacket packet input choices)

def capacities : P.calibrations.Capacities where
  side side a rectangle := (P.normalization side a rectangle).capacity

theorem primeBound (side : Bool) (a : P.support.labels side) (rectangle : Bool)
    (i : Fin ((P.seed.refinement input P.support).source side a rectangle).allocation.keep.card) :
    (P.capacities.side side a rectangle).primeBound i = 1 :=
  (P.normalization side a rectangle).capacity_primeBound i

end CanonicalMassPacket

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}

def canonicalMassData (raw : RawFamily geometry) (input : ProfileInput call)
    (choices : FullKappaChoices c p.loss)
    (packets : ∀ j : Fin raw.count, CanonicalMassPacket (raw.packet j) input choices) :
    NormalizedData call :=
  Assembly.refinedNormalizedData raw
    (fun j => (packets j).seed.ordinary)
    (fun j => (packets j).seed.refinement input (packets j).support)
    (fun j => (packets j).calibrations)
    (fun j => (packets j).capacities)

/-- N8b must prove this from the actual single coefficients and finite
labels.  The N8a ledger is consumed literally; no alternate harmonic
sum or second amplification factor is selected. -/
def NormalizedMassTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ frame : SourceFrame, ∃ cost : UniformCost,
    ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      cost.Ready call input → ∀ (trace : SourceTrace call p), trace.Realizes →
      ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
      ∀ raw : RawFamily geometry, raw.Realizes →
      ∀ (choices : FullKappaChoices c p.loss)
        (packets : ∀ j : Fin raw.count, CanonicalMassPacket (raw.packet j) input choices),
        (canonicalMassData raw input choices packets).arithmeticMass ≤
          cost.value input.amplitude call.request.height *
            call.base ^ (recipeInductionEdgeLoss c / 2 - 2 * p.loss) * raw.indexMass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CanonicalMassPacket.primeBound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.canonicalMassData
