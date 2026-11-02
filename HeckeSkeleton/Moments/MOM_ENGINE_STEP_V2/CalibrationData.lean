import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ArithmeticData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Individual arithmetic calibrations with fixed finite source costs

The base calibration binds one original ideal or prime at a time. Its
three numerical costs are fixed here to the actual finite maxima, so a
later uniform mass statement cannot be invalidated by arbitrarily
enlarging an otherwise valid calibration. Global smooth representatives
are specified separately by `GlobalProfileDictionary`.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {H : Type} {k : ℕ}

namespace SourceCost

variable (s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k)

def row : ℝ := ((s.rows.sup (fun h => ‖s.weight h‖₊) : NNReal) : ℝ)

def scalar : ℝ :=
  ((s.rows.sup (fun h => ‖s.frozenScalar (σ := Arithmetic.embedding c) h‖₊ ^ 2) : NNReal) : ℝ)

def fiber : ℕ :=
  s.rows.sup (fun h =>
    (s.rows.filter (fun j => (s.row j).momentIdeal = (s.row h).momentIdeal)).card)

end SourceCost

/-- The source remains the original allocated source. Both its moment
dictionary and its complete moving recipe precede all normalizations. -/
structure OriginalCalibration (call : Call c)
    (s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k) where
  calibration : s.Calibration (σ := Arithmetic.embedding c)
    c.family.omega (targetCharacter K c)
  recipe : CompleteMovingRowRecipe (Arithmetic.data c)
    (probeData K c) (momentRowCharacters K c) calibration.data
  normProfiles : NormProfileRecipe calibration.data
  base_eq : s.base = call.base
  kappa_eq : calibration.parameters.κ = call.node.parameters.κ
  originalSlots : OriginalSlotDictionary call.node.data s.length
  theta_eq : ∀ ξ, (calibration.data ξ).theta = call.node.data.theta
  slot_characters : ∀ ξ i, (calibration.data ξ).slotCoefficient i ∈ call.node.data.theta
  row_cost : calibration.rowBound = SourceCost.row s
  scalar_cost : calibration.scalarBound = SourceCost.scalar s
  fiber_cost : calibration.fiberBound = SourceCost.fiber s

namespace OriginalCalibration

variable {call : Call c}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable (D : OriginalCalibration call s)

/-- The source identity is global in each real profile argument. The
shape and scalar allowance are supplied before choosing the dictionary. -/
abbrev RawDictionary (input : ProfileInput call) (shape : ProfileShape)
    (scalarBound : ℝ) (window : Set ℝ) :=
  GlobalProfileDictionary input D.calibration.data s.allocation.keep.card
    D.calibration.count shape scalarBound window

/-- Actual clipping may change the plain dilation but preserves the
original slot carrier and the named parent representatives. -/
abbrev ClippedDictionary (input : ProfileInput call) (shape : ProfileShape)
    (scalarBound : ℝ) (window : Set ℝ) :=
  GlobalProfileDictionary input D.calibration.clippedData s.allocation.keep.card
    D.calibration.count shape scalarBound window

end OriginalCalibration
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
