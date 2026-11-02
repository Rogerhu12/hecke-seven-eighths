import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding
import Lean.Elab.Command

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: imports"
    stderr.flush

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

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftIdeal"
    stderr.flush

def rightIdeal (i : AllocationColumn K packet.leaf.rightSlots) :
    (Arithmetic.data c).Exterior :=
  packet.block.rightResidual (packet.rightReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightIdeal"
    stderr.flush

def leftWhole (i : AllocationColumn K packet.leaf.leftSlots) : ℂ :=
  packet.chart.sourceLeftCoefficient (packet.leftReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftWhole"
    stderr.flush

def rightWhole (i : AllocationColumn K packet.leaf.rightSlots) : ℂ :=
  packet.chart.sourceRightCoefficient (packet.rightReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightWhole"
    stderr.flush

/-- The same finite subtype, kept reducible for its local finite instances. -/
abbrev ordinaryBranchType : Type :=
  ↥(liveSecondAllocationBranches (A := Arithmetic.data c) (Ray := PUnit.{1})
    (k := SourceClassKey.leftSlots
      (s := packet.second.stage) (LC := packet.leftCover) (RC := packet.rightCover)
      packet.key)
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.rightIdeal)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchType"
    stderr.flush

/-- The original allocation, with its existing carrier made explicit. -/
noncomputable def ordinaryBranchKey (branch : packet.ordinaryBranchType) :
    SourceClassKey.AllocationKey
      (s := packet.second.stage) (LC := packet.leftCover) (RC := packet.rightCover)
      packet.key :=
  branch.val

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchKey"
    stderr.flush

def ordinaryBranchMatches (branch : packet.ordinaryBranchType) : Prop :=
  packet.ordinaryBranchKey branch = packet.allocation

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchMatches"
    stderr.flush

/-- The original rectangle type; all source fields and the branch are unchanged. -/
def ordinaryRectanglesType
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (branch : packet.ordinaryBranchType) : Type :=
  HybridOrdinaryRectangles
    (K := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (H := Arithmetic.Orbit c) (ι := Fin packet.block.primeCount)
    (V := EngineParameter) (k := packet.leaf.leftSlots) (l := packet.leaf.rightSlots)
    packet.R PUnit.{1}
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.leftIdeal packet.rightIdeal
      (fun _ => (PUnit.unit : PUnit.{1})) (fun _ => (PUnit.unit : PUnit.{1}))
    packet.leftWhole packet.rightWhole leftPoint rightPoint branch packet.leaf.exceptional

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryRectanglesType"
    stderr.flush

def ordinaryLeftRectangleMatches
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (branch : packet.ordinaryBranchType)
    (rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K packet.leaf.leftSlots),
    i ∈ childCartesianColumns packet.leftReindex.plain₁
    packet.leftReindex.plain₂ packet.leftReindex.slots →
      rectangles.leftTerms r i = packet.originalLeftRectangle r i

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryLeftRectangleMatches"
    stderr.flush

def ordinaryRightRectangleMatches
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (branch : packet.ordinaryBranchType)
    (rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K packet.leaf.rightSlots),
    i ∈ childCartesianColumns packet.rightReindex.plain₁
    packet.rightReindex.plain₂ packet.rightReindex.slots →
      rectangles.rightTerms r i = packet.originalRightRectangle r i

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryRightRectangleMatches"
    stderr.flush

/-- A name for the same complete ordinary binding proposition. -/
def ordinaryBindingProp
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K packet.leaf.rightSlots → EngineParameter)
    (branch : packet.ordinaryBranchType)
    (rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch) : Prop :=
  ActualHybridLeaf.OrdinaryBinding
    (K := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (H := Arithmetic.Orbit c) (ι := Fin packet.block.primeCount)
    (U := ℝ) (V := ℝ) (R := packet.R) (Ray := PUnit.{1})
    (leaf := packet.leaf)
    (S₁ := packet.leftReindex.plain₁) (S₂ := packet.leftReindex.plain₂)
    (S := packet.leftReindex.slots)
    (T₁ := packet.rightReindex.plain₁) (T₂ := packet.rightReindex.plain₂)
    (T := packet.rightReindex.slots)
    (IA := packet.leftIdeal) (IB := packet.rightIdeal)
    (rayLeft := fun _ => (PUnit.unit : PUnit.{1}))
    (rayRight := fun _ => (PUnit.unit : PUnit.{1}))
    (wholeLeft := packet.leftWhole) (wholeRight := packet.rightWhole)
    (x := leftPoint) (y := rightPoint)
    (b := branch) (exceptional := packet.leaf.exceptional)
    rectangles

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBindingProp"
    stderr.flush


end RawLeafPacket

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: before structure"
    stderr.flush

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
  branch : packet.ordinaryBranchType
  branch_eq : packet.ordinaryBranchMatches branch
  rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch
  left_rectangle : packet.ordinaryLeftRectangleMatches leftPoint rightPoint branch rectangles
  right_rectangle : packet.ordinaryRightRectangleMatches leftPoint rightPoint branch rectangles
  binding : packet.ordinaryBindingProp leftPoint rightPoint branch rectangles

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: structure"
    stderr.flush

namespace OrdinaryData

variable {packet : RawLeafPacket call p} (O : OrdinaryData packet)

/-- Both sides use the same original nonexceptional rows. -/
abbrev rows (_O : OrdinaryData packet) :=
  packet.R.restrictRows (fun h => ¬packet.leaf.exceptional h)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rows"
    stderr.flush

abbrev leftFrame (rectangle : Bool) :=
  O.rectangles.leftFrame (Arithmetic.context c) rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftFrame"
    stderr.flush

abbrev rightFrame (rectangle : Bool) :=
  O.rectangles.rightFrame (Arithmetic.context c) rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightFrame"
    stderr.flush

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchKey
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchMatches
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryRectanglesType
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBindingProp
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.leftFrame
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.rightFrame
