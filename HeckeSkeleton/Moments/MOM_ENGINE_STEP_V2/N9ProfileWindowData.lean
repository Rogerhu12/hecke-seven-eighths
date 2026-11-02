import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FullKappaContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileWindowContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact data joining the N5b windows to the N6 capacities

The complete family below consists of the individual N6 results on
the original N5b windows.  Its capacities are projected from those
results.  The original sources, passive labels and normalizers remain
the ones in the same refinement data.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField MeasureTheory EngineStep
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}

namespace UniformProfileWindowCertificate

variable {frame : SourceFrame} {shape : ProfileShape} {orders : Finset (ℕ × ℕ)}

/-- N3's actual scalar allowance is one.  N5b's active cost is therefore
exactly a fixed constant times the original input amplitude. -/
def kernelInputCost (certificate : UniformProfileWindowCertificate c frame shape orders) :
    UniformCost where
  orders := certificate.inputOrders
  coefficient := 2 * certificate.costCoefficient
  coefficient_nonneg := mul_nonneg (by norm_num) certificate.costCoefficient_pos.le
  profileDegree := 1
  heightDegree := 0
  heightDegree_nonneg := le_rfl
  threshold := 1
  threshold_one_le := le_rfl

end UniformProfileWindowCertificate

namespace RawClippedProfileWindows

variable {H : Type} {k : ℕ}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter H k}
variable {D : OriginalCalibration call s} {rawCoefficient uniformCost : ℝ} {degree : ℕ}
variable {orders : Finset (ℕ × ℕ)}

/-- N6 uses the coefficient selected at the common fixed order set and
the same original representatives.  Only the seminorm assertions are
restricted to the requested recursive child orders. -/
def toFullKappaWindows
    (windows : RawClippedProfileWindows D orders rawCoefficient uniformCost degree)
    (horders : call.childOrders ⊆ orders) :
    FullKappaWindows D (D.profileRadiusCoefficient orders rawCoefficient)
      degree degree where
  coefficient_nonneg := windows.coefficient_nonneg
  raw ξ := (windows.original ξ).restrictOrders horders
  clipped ξ := (windows.clipped ξ).restrictOrders horders

end RawClippedProfileWindows

namespace RefinementData.Calibrations

variable {p : SourceParameters c} {input : ProfileInput call}
variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable {R : RefinementData O input} (C : R.Calibrations)

abbrev ProfileWindows (orders : Finset (ℕ × ℕ))
    (rawCoefficient uniformCost : ℝ) (degree : ℕ) :=
  ∀ side a rectangle, RawClippedProfileWindows (C.side side a rectangle)
    orders rawCoefficient uniformCost degree

variable {rawCoefficient uniformCost loss : ℝ} {degree : ℕ}
variable {orders : Finset (ℕ × ℕ)}

abbrev FullKappaResults (choices : FullKappaChoices c loss)
    (horders : call.childOrders ⊆ orders)
    (windows : C.ProfileWindows orders rawCoefficient uniformCost degree) :=
  ∀ side a rectangle,
    Σ geometry : SideGeometryData packet.R side (R.source side a rectangle)
      (C.side side a rectangle),
      FullKappaSideResult choices geometry
        ((windows side a rectangle).toFullKappaWindows horders)

/-- The chosen capacities are exactly the projections of these N6
results, with no independent capacity or replacement radius. -/
def fullKappaCapacities {choices : FullKappaChoices c loss}
    {horders : call.childOrders ⊆ orders}
    {windows : C.ProfileWindows orders rawCoefficient uniformCost degree}
    (results : C.FullKappaResults choices horders windows) : C.Capacities where
  side side a rectangle := (results side a rectangle).2.capacity

end RefinementData.Calibrations
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
