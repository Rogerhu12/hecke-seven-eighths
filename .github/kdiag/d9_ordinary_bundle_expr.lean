import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding
import Lean

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


set_option genInjectivity false in
set_option genSizeOf false in
/-- Canonical source data used by the ordinary rectangle construction.
The packet below supplies every field from its original physical source. -/
structure OrdinarySourceInputs (c : TargetContext K) where
  leaf : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ
  primeCount : ℕ
  rowData : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c)
    (Arithmetic.Orbit c) (Fin primeCount)
  leftPlain₁ : Finset (Ideal (𝓞 K))
  leftPlain₂ : Finset (Ideal (𝓞 K))
  leftPrimes : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))
  rightPlain₁ : Finset (Ideal (𝓞 K))
  rightPlain₂ : Finset (Ideal (𝓞 K))
  rightPrimes : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))
  leftIdeal : AllocationColumn K leaf.leftSlots → (Arithmetic.data c).Exterior
  rightIdeal : AllocationColumn K leaf.rightSlots → (Arithmetic.data c).Exterior
  leftWhole : AllocationColumn K leaf.leftSlots → ℂ
  rightWhole : AllocationColumn K leaf.rightSlots → ℂ
  originalLeftRectangle : Bool → AllocationColumn K leaf.leftSlots → ℂ
  originalRightRectangle : Bool → AllocationColumn K leaf.rightSlots → ℂ

namespace OrdinarySourceInputs

variable (I : OrdinarySourceInputs c)

abbrev branchType : Type :=
  ↥(liveSecondAllocationBranches (A := Arithmetic.data c) (Ray := PUnit.{1})
    (k := I.leaf.leftSlots)
    I.leftPlain₁ I.leftPlain₂ I.leftPrimes
    I.rightPlain₁ I.rightPlain₂ I.rightPrimes I.rightIdeal)

def rectanglesType
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType) : Type :=
  HybridOrdinaryRectangles
    (K := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (H := Arithmetic.Orbit c) (ι := Fin I.primeCount)
    (V := EngineParameter) (k := I.leaf.leftSlots) (l := I.leaf.rightSlots)
    I.rowData PUnit.{1}
    I.leftPlain₁ I.leftPlain₂ I.leftPrimes
    I.rightPlain₁ I.rightPlain₂ I.rightPrimes
    I.leftIdeal I.rightIdeal
    (fun _ => (PUnit.unit : PUnit.{1})) (fun _ => (PUnit.unit : PUnit.{1}))
    I.leftWhole I.rightWhole leftPoint rightPoint branch I.leaf.exceptional

def leftRectangleMatches
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType)
    (rectangles : I.rectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K I.leaf.leftSlots),
    i ∈ childCartesianColumns I.leftPlain₁ I.leftPlain₂ I.leftPrimes →
      rectangles.leftTerms r i = I.originalLeftRectangle r i

def rightRectangleMatches
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType)
    (rectangles : I.rectanglesType leftPoint rightPoint branch) : Prop :=
  ∀ (r : Bool) (i : AllocationColumn K I.leaf.rightSlots),
    i ∈ childCartesianColumns I.rightPlain₁ I.rightPlain₂ I.rightPrimes →
      rectangles.rightTerms r i = I.originalRightRectangle r i

def bindingProp
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType)
    (rectangles : I.rectanglesType leftPoint rightPoint branch) : Prop :=
  ActualHybridLeaf.OrdinaryBinding
    (K := K) (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
    (H := Arithmetic.Orbit c) (ι := Fin I.primeCount)
    (U := ℝ) (V := ℝ) (R := I.rowData) (Ray := PUnit.{1})
    (leaf := I.leaf)
    (S₁ := I.leftPlain₁) (S₂ := I.leftPlain₂) (S := I.leftPrimes)
    (T₁ := I.rightPlain₁) (T₂ := I.rightPlain₂) (T := I.rightPrimes)
    (IA := I.leftIdeal) (IB := I.rightIdeal)
    (rayLeft := fun _ => (PUnit.unit : PUnit.{1}))
    (rayRight := fun _ => (PUnit.unit : PUnit.{1}))
    (wholeLeft := I.leftWhole) (wholeRight := I.rightWhole)
    (x := leftPoint) (y := rightPoint)
    (b := branch) (exceptional := I.leaf.exceptional) rectangles

abbrev rows :=
  I.rowData.restrictRows (fun h => ¬I.leaf.exceptional h)

abbrev leftFrame
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType)
    (rectangles : I.rectanglesType leftPoint rightPoint branch)
    (comparison : Bool) :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
      I.rows PUnit.{1} .left I.leaf.leftSlots :=
  rectangles.leftFrame (Arithmetic.context c) comparison

abbrev rightFrame
    (leftPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.leftSlots → EngineParameter)
    (rightPoint : Arithmetic.Orbit c →
      AllocationColumn K I.leaf.rightSlots → EngineParameter)
    (branch : I.branchType)
    (rectangles : I.rectanglesType leftPoint rightPoint branch)
    (comparison : Bool) :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
      I.rows PUnit.{1} .right I.leaf.rightSlots :=
  rectangles.rightFrame (Arithmetic.context c) comparison

end OrdinarySourceInputs

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: OrdinarySourceInputs"
    stderr.flush

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


/-- Every field is copied from the fixed original packet. This wrapper
introduces no new choices, predicates, coefficients or source carriers. -/
def ordinaryInputs : OrdinarySourceInputs c := by
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.instantiateMVars (← goal.getType)
      let .const inputName levels := target.getAppFn
        | throwError "expected the original ordinary input record"
      unless inputName == ``OrdinarySourceInputs do
        throwError "unexpected ordinary input record"
      let fields := #[
        (← `(packet.leaf)), (← `(packet.block.primeCount)), (← `(packet.R)),
        (← `(packet.leftReindex.plain₁)), (← `(packet.leftReindex.plain₂)),
        (← `(packet.leftReindex.slots)),
        (← `(packet.rightReindex.plain₁)), (← `(packet.rightReindex.plain₂)),
        (← `(packet.rightReindex.slots)),
        (← `(packet.leftIdeal)), (← `(packet.rightIdeal)),
        (← `(packet.leftWhole)), (← `(packet.rightWhole)),
        (← `(packet.originalLeftRectangle)), (← `(packet.originalRightRectangle))]
      let mut args := target.getAppArgs
      for field in fields do
        args := args.push (← Lean.Elab.Tactic.elabTerm field none)
      goal.assign (Lean.mkAppN (Lean.mkConst ``OrdinarySourceInputs.mk levels) args)
      Lean.Elab.Tactic.replaceMainGoal []

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryInputs"
    stderr.flush

/-- The same finite subtype, kept reducible for its local finite instances. -/
abbrev ordinaryBranchType : Type :=
  packet.ordinaryInputs.branchType

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
  by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let goal ← Lean.Elab.Tactic.getMainGoal
        let lctx := (← goal.getDecl).lctx
        let some b := lctx.findFromUserName? `branch
          | throwError "original ordinary branch not found"
        goal.assign (Lean.Expr.proj ``Subtype 0 (Lean.mkFVar b.fvarId))
        Lean.Elab.Tactic.replaceMainGoal []

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
  packet.ordinaryInputs.rectanglesType leftPoint rightPoint branch

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
  packet.ordinaryInputs.leftRectangleMatches leftPoint rightPoint branch rectangles

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
  packet.ordinaryInputs.rightRectangleMatches leftPoint rightPoint branch rectangles

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
  packet.ordinaryInputs.bindingProp leftPoint rightPoint branch rectangles

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
  packet.ordinaryInputs.leftFrame O.leftPoint O.rightPoint O.branch O.rectangles rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftFrame"
    stderr.flush

abbrev rightFrame (rectangle : Bool) :=
  packet.ordinaryInputs.rightFrame O.leftPoint O.rightPoint O.branch O.rectangles rectangle

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightFrame"
    stderr.flush

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryInputs
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchKey
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.leftFrame
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.rightFrame


#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.mk

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames : Array Name := env.header.moduleNames
  let nsPrefix : Name := `HeckeSkeleton.Moments.EngineStepV2
  let modulePrefix : Name := `HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2
  let moduleOf (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    moduleNames[idx.toNat]?
  let names := (env.constants.toList.filterMap fun (name, _) =>
    if nsPrefix.isPrefixOf (privateToUserName name) ||
        (moduleOf name).any (modulePrefix.isPrefixOf ·)
    then some name else none).toArray.qsort Name.lt
  unless !names.isEmpty do
    throwError "No loaded V2 declarations found"
  let required : Array Name := #[
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchKey,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchMatches,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.leftFrame,
    `HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.rightFrame]
  for name in required do
    let some (.defnInfo _) := env.find? name
      | throwError "Required ordinary definition is missing: {name}"
    unless names.contains name do
      throwError "Required ordinary definition is outside the audit: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let dependencies ← collectAxioms name
    let extra := dependencies.filter fun ax => !permitted.contains ax
    unless extra.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {extra}"
    logInfo m!"AXIOMS {name}: {dependencies}"
  logInfo m!"D_COMPLETE_FILE_PASSED: {names.size} declarations"
