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
    (k := packet.leaf.leftSlots)
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.rightIdeal)

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchType"
    stderr.flush

/-- Keep the actual live branch in its original, short named carrier.
The allocation is the `val` field of this branch.  In particular this
definition performs no conversion between two presentations of its
dependent allocation type. -/
noncomputable def ordinaryBranchKey (branch : packet.ordinaryBranchType) :
    packet.ordinaryBranchType :=
  branch

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchKey"
    stderr.flush

/-- The branch retains the original allocation.  The two carriers are
definitionally equal, but heterogeneous equality states their identity
without asking elaboration to compare the expanded presentations. -/
def ordinaryBranchMatches (branch : packet.ordinaryBranchType) : Prop :=
  HEq (packet.ordinaryBranchKey branch).val packet.allocation

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

abbrev leftFrame (O : OrdinaryData packet) (rectangle : Bool) :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
      O.rows PUnit.{1} .left packet.leaf.leftSlots := by
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let lctx := (← g.getDecl).lctx
      let some o := lctx.findFromUserName? `O
        | throwError "original ordinary datum not found"
      let some r := lctx.findFromUserName? `rectangle
        | throwError "original rectangle selector not found"
      let rectangles := Lean.Expr.proj
        ``HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData 4
        (Lean.mkFVar o.fvarId)
      let rectanglesType ← Lean.Meta.withTransparency .all do
        Lean.Meta.whnf (← Lean.Meta.inferType rectangles)
      let context ← Lean.Elab.Tactic.elabTerm (← `(Arithmetic.context c)) none
      let contextType ← Lean.Meta.withTransparency .all do
        Lean.Meta.whnf (← Lean.Meta.inferType context)
      let frameName := ``HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.leftFrame
      let frameInfo ← Lean.getConstInfo frameName
      -- Every actual type parameter here lies in Type 0. The constructed
      -- expression is subsequently checked by the ordinary declaration kernel.
      let levels := frameInfo.levelParams.map (fun _ => Lean.Level.zero)
      let frameType := frameInfo.type.instantiateLevelParams frameInfo.levelParams levels
      Lean.Meta.forallTelescope frameType fun xs _ => do
        unless xs.size ≥ 3 do
          throwError "unexpected frame telescope"
        let b := xs[xs.size - 3]!
        let a := xs[xs.size - 2]!
        let bType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType b)
        let aType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType a)
        let mut bindings : Array (Lean.Expr × Lean.Expr) := #[]
        for (template, actual) in #[(bType, rectanglesType), (aType, contextType)] do
          unless template.getAppFn == actual.getAppFn do
            throwError "frame input type head differs from the original"
          let genericArgs := template.getAppArgs
          let actualArgs := actual.getAppArgs
          unless genericArgs.size == actualArgs.size do
            throwError "frame input type arity differs from the original"
          for i in [:genericArgs.size] do
            let parameter := genericArgs[i]!
            if parameter.isFVar then
              if !(bindings.any (fun p => p.1 == parameter)) then
                bindings := bindings.push (parameter, actualArgs[i]!)
            -- Derived arguments may contain generic parameters. Recover only
            -- direct parameters here; the final ordinary kernel check handles
            -- all derived arguments after the application is reconstructed.
        let mut args : Array Lean.Expr := #[]
        for i in [:xs.size] do
          if i == xs.size - 3 then
            args := args.push rectangles
          else if i == xs.size - 2 then
            args := args.push context
          else if i == xs.size - 1 then
            args := args.push (Lean.mkFVar r.fvarId)
          else
            let some pair := bindings.find? (fun p => p.1 == xs[i]!)
              | throwError "an original frame parameter was not recovered"
            args := args.push pair.2
        let value := Lean.mkAppN (Lean.mkConst frameName levels) args
        -- The original public result type is checked against this original
        -- function application by the normal declaration kernel.
        g.assign value
        Lean.Elab.Tactic.replaceMainGoal []

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: leftFrame"
    stderr.flush

abbrev rightFrame (O : OrdinaryData packet) (rectangle : Bool) :
    SecondSideFrame (V := EngineParameter) (Arithmetic.context c)
      O.rows PUnit.{1} .right packet.leaf.rightSlots := by
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let lctx := (← g.getDecl).lctx
      let some o := lctx.findFromUserName? `O
        | throwError "original ordinary datum not found"
      let some r := lctx.findFromUserName? `rectangle
        | throwError "original rectangle selector not found"
      let rectangles := Lean.Expr.proj
        ``HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData 4
        (Lean.mkFVar o.fvarId)
      let rectanglesType ← Lean.Meta.withTransparency .all do
        Lean.Meta.whnf (← Lean.Meta.inferType rectangles)
      let context ← Lean.Elab.Tactic.elabTerm (← `(Arithmetic.context c)) none
      let contextType ← Lean.Meta.withTransparency .all do
        Lean.Meta.whnf (← Lean.Meta.inferType context)
      let frameName := ``HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.rightFrame
      let frameInfo ← Lean.getConstInfo frameName
      -- Every actual type parameter here lies in Type 0. The constructed
      -- expression is subsequently checked by the ordinary declaration kernel.
      let levels := frameInfo.levelParams.map (fun _ => Lean.Level.zero)
      let frameType := frameInfo.type.instantiateLevelParams frameInfo.levelParams levels
      Lean.Meta.forallTelescope frameType fun xs _ => do
        unless xs.size ≥ 3 do
          throwError "unexpected frame telescope"
        let b := xs[xs.size - 3]!
        let a := xs[xs.size - 2]!
        let bType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType b)
        let aType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType a)
        let mut bindings : Array (Lean.Expr × Lean.Expr) := #[]
        for (template, actual) in #[(bType, rectanglesType), (aType, contextType)] do
          unless template.getAppFn == actual.getAppFn do
            throwError "frame input type head differs from the original"
          let genericArgs := template.getAppArgs
          let actualArgs := actual.getAppArgs
          unless genericArgs.size == actualArgs.size do
            throwError "frame input type arity differs from the original"
          for i in [:genericArgs.size] do
            let parameter := genericArgs[i]!
            if parameter.isFVar then
              if !(bindings.any (fun p => p.1 == parameter)) then
                bindings := bindings.push (parameter, actualArgs[i]!)
            -- Derived arguments may contain generic parameters. Recover only
            -- direct parameters here; the final ordinary kernel check handles
            -- all derived arguments after the application is reconstructed.
        let mut args : Array Lean.Expr := #[]
        for i in [:xs.size] do
          if i == xs.size - 3 then
            args := args.push rectangles
          else if i == xs.size - 2 then
            args := args.push context
          else if i == xs.size - 1 then
            args := args.push (Lean.mkFVar r.fvarId)
          else
            let some pair := bindings.find? (fun p => p.1 == xs[i]!)
              | throwError "an original frame parameter was not recovered"
            args := args.push pair.2
        let value := Lean.mkAppN (Lean.mkConst frameName levels) args
        -- The original public result type is checked against this original
        -- function application by the normal declaration kernel.
        g.assign value
        Lean.Elab.Tactic.replaceMainGoal []

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: rightFrame"
    stderr.flush

end OrdinaryData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchKey
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchMatches


#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.leftFrame
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.rightFrame


namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

/-- This is the original allocation-valued map. The expression is the
ordinary `Subtype.val` projection, checked by the declaration kernel. -/
def ordinaryBranchAllocation (branch : packet.ordinaryBranchType) :
    SourceClassKey.AllocationKey
      (s := packet.second.stage) (LC := packet.leftCover) (RC := packet.rightCover)
      packet.key := by
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
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchAllocation"
    stderr.flush

/-- The HEq form is equivalent to the original allocation equality,
without any additional mathematical assumption. -/
theorem ordinaryBranchMatches_iff_original (branch : packet.ordinaryBranchType) :
    packet.ordinaryBranchMatches branch ↔
      packet.ordinaryBranchAllocation branch = packet.allocation := by
  run_tac
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.instantiateMVars (← goal.getType)
      unless target.isAppOfArity ``Iff 2 do
        throwError "expected the unchanged matching equivalence"
      let sides := target.getAppArgs
      let left := sides[0]!
      let right := sides[1]!
      unless right.isAppOfArity ``Eq 3 do
        throwError "expected the original allocation equality"
      let eqArgs := right.getAppArgs
      let carrier := eqArgs[0]!
      let lhs := eqArgs[1]!
      let rhs := eqArgs[2]!
      let carrierSort ← Lean.Meta.whnf (← Lean.Meta.inferType carrier)
      let .sort level := carrierSort
        | throwError "the original allocation carrier is not a sort"
      -- All theorem arguments come from the original equality in the goal.
      -- No metavariable unification or getFunInfo call is needed to construct
      -- these applications. The ordinary kernel checks the complete proof.
      let forward := Lean.Expr.lam `h left
        (Lean.mkAppN (Lean.mkConst ``eq_of_heq [level])
          #[carrier, lhs, rhs, Lean.Expr.bvar 0]) .default
      let backward := Lean.Expr.lam `h right
        (Lean.mkAppN (Lean.mkConst ``heq_of_eq [level])
          #[carrier, lhs, rhs, Lean.Expr.bvar 0]) .default
      goal.assign
        (Lean.mkAppN (Lean.mkConst ``Iff.intro)
          #[left, right, forward, backward])
      Lean.Elab.Tactic.replaceMainGoal []

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 OrdinaryData checkpoint: ordinaryBranchMatches_iff_original"
    stderr.flush

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchAllocation
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryBranchMatches_iff_original


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
