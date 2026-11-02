import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Individual ordinary rectangles of an original finite leaf

The original row set, complete correlation, column carriers, whole
coefficients, exceptional predicate and allocation label are fixed by
the actual source key. Only the individual rectangle factorizations and
their Fourier-location dictionaries remain to be constructed by the
atom task. This record asserts no capacity or profile estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global WholeAllocation

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def leftIdeal (i : AllocationColumn K packet.leaf.leftSlots) :
    (Arithmetic.data c).Exterior :=
  packet.block.leftResidual (packet.leftReindex.index i)

def rightIdeal (i : AllocationColumn K packet.leaf.rightSlots) :
    (Arithmetic.data c).Exterior :=
  packet.block.rightResidual (packet.rightReindex.index i)

def leftWhole (i : AllocationColumn K packet.leaf.leftSlots) : ℂ :=
  packet.chart.sourceLeftCoefficient (packet.leftReindex.index i)

def rightWhole (i : AllocationColumn K packet.leaf.rightSlots) : ℂ :=
  packet.chart.sourceRightCoefficient (packet.rightReindex.index i)

end RawLeafPacket

set_option diagnostics true in
set_option genInjectivity false in
set_option genSizeOf false in
/-- The independent divisor allocation is the original one. The
single-atom binding permits the common row translation which cancels
inside the polynomial norm, before either continuous integration. -/
structure OrdinaryData (packet : RawLeafPacket call p) where
  leftPoint : Arithmetic.Orbit c →
    AllocationColumn K packet.leaf.leftSlots → EngineParameter
  rightPoint : Arithmetic.Orbit c →
    AllocationColumn K packet.leaf.rightSlots → EngineParameter
  branch : liveSecondAllocationBranches (Ray := PUnit.{1})
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.rightIdeal
  branch_eq : branch.val = packet.allocation
  rectangles : HybridOrdinaryRectangles packet.R PUnit.{1}
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.leftIdeal packet.rightIdeal
      (fun _ => (PUnit.unit : PUnit.{1})) (fun _ => (PUnit.unit : PUnit.{1}))
    packet.leftWhole packet.rightWhole leftPoint rightPoint branch packet.leaf.exceptional
  left_rectangle : ∀ r i, i ∈ childCartesianColumns packet.leftReindex.plain₁
    packet.leftReindex.plain₂ packet.leftReindex.slots →
      rectangles.leftTerms r i = packet.originalLeftRectangle r i
  right_rectangle : ∀ r i, i ∈ childCartesianColumns packet.rightReindex.plain₁
    packet.rightReindex.plain₂ packet.rightReindex.slots →
      rectangles.rightTerms r i = packet.originalRightRectangle r i
  binding : packet.leaf.OrdinaryBinding rectangles

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

/-- Both sides use the same original nonexceptional rows. -/
abbrev rows (_O : OrdinaryData packet) :=
  packet.R.restrictRows (fun h => ¬packet.leaf.exceptional h)

abbrev leftFrame (rectangle : Bool) :=
  O.rectangles.leftFrame (Arithmetic.context c) rectangle

abbrev rightFrame (rectangle : Bool) :=
  O.rectangles.rightFrame (Arithmetic.context c) rectangle

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
