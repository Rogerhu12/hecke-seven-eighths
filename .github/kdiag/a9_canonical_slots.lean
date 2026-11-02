import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding
import Lean.Elab.Command
import Lean.Util.CollectAxioms

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

theorem leaf_leftSlots_eq :
    packet.leaf.leftSlots = SourceClassKey.leftSlots packet.key := rfl

theorem leaf_rightSlots_eq :
    packet.leaf.rightSlots = SourceClassKey.rightSlots packet.key := rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: slot equalities"
    stderr.flush

def leftIdeal (i : AllocationColumn K (SourceClassKey.leftSlots packet.key)) :
    (Arithmetic.data c).Exterior :=
  packet.block.leftResidual (packet.leftReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftIdeal"
    stderr.flush

def rightIdeal (i : AllocationColumn K (SourceClassKey.rightSlots packet.key)) :
    (Arithmetic.data c).Exterior :=
  packet.block.rightResidual (packet.rightReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightIdeal"
    stderr.flush

def leftWhole (i : AllocationColumn K (SourceClassKey.leftSlots packet.key)) : ℂ :=
  packet.chart.sourceLeftCoefficient (packet.leftReindex.index i)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftWhole"
    stderr.flush

def rightWhole (i : AllocationColumn K (SourceClassKey.rightSlots packet.key)) : ℂ :=
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
      AllocationColumn K (SourceClassKey.leftSlots packet.key) → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K (SourceClassKey.rightSlots packet.key) → EngineParameter)
    (branch : packet.ordinaryBranchType) : Type :=
  HybridOrdinaryRectangles
    (K := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (H := Arithmetic.Orbit c) (ι := Fin packet.block.primeCount)
    (V := EngineParameter) (k := (SourceClassKey.leftSlots packet.key)) (l := (SourceClassKey.rightSlots packet.key))
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
      AllocationColumn K (SourceClassKey.leftSlots packet.key) → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K (SourceClassKey.rightSlots packet.key) → EngineParameter)
    (branch : packet.ordinaryBranchType)
    (rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K (SourceClassKey.leftSlots packet.key)),
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
      AllocationColumn K (SourceClassKey.leftSlots packet.key) → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K (SourceClassKey.rightSlots packet.key) → EngineParameter)
    (branch : packet.ordinaryBranchType)
    (rectangles : packet.ordinaryRectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K (SourceClassKey.rightSlots packet.key)),
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
      AllocationColumn K (SourceClassKey.leftSlots packet.key) → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K (SourceClassKey.rightSlots packet.key) → EngineParameter)
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
    AllocationColumn K (SourceClassKey.leftSlots packet.key) → EngineParameter
  rightPoint : Arithmetic.Orbit c →
    AllocationColumn K (SourceClassKey.rightSlots packet.key) → EngineParameter
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

/-- A short name for the original left frame type. -/
def LeftFrameType : Type :=
  SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
    O.rows PUnit.{1} .left (SourceClassKey.leftSlots packet.key)

/-- A short name for the original right frame type. -/
def RightFrameType : Type :=
  SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
    O.rows PUnit.{1} .right (SourceClassKey.rightSlots packet.key)

def leftFrame (rectangle : Bool) : LeftFrameType O :=
  O.rectangles.leftFrame (Arithmetic.context c) rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftFrame"
    stderr.flush

def rightFrame (rectangle : Bool) : RightFrameType O :=
  O.rectangles.rightFrame (Arithmetic.context c) rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightFrame"
    stderr.flush

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let moduleNames := env.header.moduleNames
  let moduleOf (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    moduleNames[idx.toNat]?
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) ||
        (moduleOf name).any (modulePrefix.isPrefixOf ·) then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
  logInfo m!"V2_FIX_A_AXIOMS_PASSED: {names.size} declarations"
