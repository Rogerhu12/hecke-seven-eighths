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

open Lean Meta Elab Tactic

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
  by
    run_tac do
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let mut branchExpr : Option Lean.Expr := none
        for decl in (← getLCtx) do
          if decl.userName == `branch then
            branchExpr := some decl.toExpr
        let some branchExpr := branchExpr | throwError "ordinary branch not found"
        goal.assign (Lean.Expr.proj ``Subtype 0 branchExpr)
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
  by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let g ← Lean.Elab.Tactic.getMainGoal
        let mut values : Array (Lean.Name × Lean.Expr) := #[]
        let e ← Lean.Elab.Tactic.elabTerm (← `(K)) none
        values := values.push (`K, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter K"
        let e ← Lean.Elab.Tactic.elabTerm (← `(Arithmetic.data c)) none
        values := values.push (`A, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter A"
        let e ← Lean.Elab.Tactic.elabTerm (← `(Arithmetic.embedding c)) none
        values := values.push (`σ, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter σ"
        let e ← Lean.Elab.Tactic.elabTerm (← `(Arithmetic.Orbit c)) none
        values := values.push (`H, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter H"
        let e ← Lean.Elab.Tactic.elabTerm (← `(Fin packet.block.primeCount)) none
        values := values.push (`ι, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter ι"
        let e ← Lean.Elab.Tactic.elabTerm (← `(EngineParameter)) none
        values := values.push (`V, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter V"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leaf.leftSlots)) none
        values := values.push (`k, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter k"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leaf.rightSlots)) none
        values := values.push (`l, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter l"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.R)) none
        values := values.push (`R, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter R"
        let e ← Lean.Elab.Tactic.elabTerm (← `(PUnit.{1})) none
        values := values.push (`Ray, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter Ray"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leftReindex.plain₁)) none
        values := values.push (`S₁, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter S₁"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leftReindex.plain₂)) none
        values := values.push (`S₂, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter S₂"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leftReindex.slots)) none
        values := values.push (`S, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter S"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.rightReindex.plain₁)) none
        values := values.push (`T₁, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter T₁"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.rightReindex.plain₂)) none
        values := values.push (`T₂, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter T₂"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.rightReindex.slots)) none
        values := values.push (`T, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter T"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leftIdeal)) none
        values := values.push (`IA, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter IA"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.rightIdeal)) none
        values := values.push (`IB, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter IB"
        let e ← Lean.Elab.Tactic.elabTerm (← `(fun _ : AllocationColumn K packet.leaf.leftSlots => (PUnit.unit : PUnit.{1}))) none
        values := values.push (`rayLeft, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter rayLeft"
        let e ← Lean.Elab.Tactic.elabTerm (← `(fun _ : AllocationColumn K packet.leaf.rightSlots => (PUnit.unit : PUnit.{1}))) none
        values := values.push (`rayRight, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter rayRight"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leftWhole)) none
        values := values.push (`wholeLeft, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter wholeLeft"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.rightWhole)) none
        values := values.push (`wholeRight, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter wholeRight"
        let e ← Lean.Elab.Tactic.elabTerm (← `(leftPoint)) none
        values := values.push (`x, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter x"
        let e ← Lean.Elab.Tactic.elabTerm (← `(rightPoint)) none
        values := values.push (`y, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter y"
        let e ← Lean.Elab.Tactic.elabTerm (← `(branch)) none
        values := values.push (`b, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter b"
        let e ← Lean.Elab.Tactic.elabTerm (← `(packet.leaf.exceptional)) none
        values := values.push (`exceptional, e)
        IO.eprintln "KDIAG ordinaryRectanglesType parameter exceptional"
        let typeName := ``HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles
        let info ← Lean.getConstInfo typeName
        let levels := info.levelParams.map (fun _ => Lean.Level.zero)
        let ty := info.type.instantiateLevelParams info.levelParams levels
        Lean.Meta.forallTelescope ty fun xs _ => do
          -- Recover the exact row-carried instances, rather than asking the
          -- typeclass synthesizer to choose another presentation of them.
          let some rowValue := values.find? (fun v => v.1 == `R)
            | throwError "original correlation rows not found"
          let mut rowParameter : Option Lean.Expr := none
          for x in xs do
            if (← x.fvarId!.getDecl).userName == `R then
              rowParameter := some x
          let some rowParameter := rowParameter
            | throwError "original correlation row parameter not found"
          let genericRows ← Lean.Meta.withTransparency .all do
            Lean.Meta.whnf (← Lean.Meta.inferType rowParameter)
          let actualRows ← Lean.Meta.withTransparency .all do
            Lean.Meta.whnf (← Lean.Meta.inferType rowValue.2)
          unless genericRows.getAppFn == actualRows.getAppFn do
            throwError "original correlation row type head changed"
          let genericRowArgs := genericRows.getAppArgs
          let actualRowArgs := actualRows.getAppArgs
          unless genericRowArgs.size == actualRowArgs.size do
            throwError "original correlation row type arity changed"
          let mut rowBindings : Array (Lean.Expr × Lean.Expr) := #[]
          for i in [:genericRowArgs.size] do
            if genericRowArgs[i]!.isFVar then
              rowBindings := rowBindings.push (genericRowArgs[i]!, actualRowArgs[i]!)
          let mut args : Array Lean.Expr := #[]
          for i in [:xs.size] do
            let d ← xs[i]!.fvarId!.getDecl
            let actualType := d.type.replaceFVars (xs.extract 0 i) args
            let arg ← match values.find? (fun v => v.1 == d.userName) with
              | some pair => pure pair.2
              | none =>
                match rowBindings.find? (fun v => v.1 == xs[i]!) with
                | some pair => pure pair.2
                | none =>
                  if d.binderInfo == Lean.BinderInfo.instImplicit then
                    Lean.Meta.synthInstance actualType
                  else
                    throwError "unmapped rectangle parameter {d.userName}"
            args := args.push arg
          -- This is precisely the original structure type applied to its
          -- original parameters. The ordinary declaration kernel checks it.
          g.assign (Lean.mkAppN (Lean.mkConst typeName levels) args)
          Lean.Elab.Tactic.replaceMainGoal []

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
  by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let g ← Lean.Elab.Tactic.getMainGoal
        let some rectangles := (← g.getDecl).lctx.findFromUserName? `rectangles
          | throwError "original rectangles local variable not found"
        let terms := Lean.Expr.proj
          ``HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles 0
          (Lean.mkFVar rectangles.fvarId)
        let original ← Lean.Elab.Tactic.elabTerm
          (← `(packet.originalLeftRectangle)) none
        let columns ← Lean.Elab.Tactic.elabTerm
          (← `(childCartesianColumns packet.leftReindex.plain₁
            packet.leftReindex.plain₂ packet.leftReindex.slots)) none
        let termsType ← Lean.Meta.inferType terms
        Lean.Meta.forallTelescope termsType fun xs _ => do
          unless xs.size == 2 do
            throwError "original rectangle terms must take comparison and column"
          let columnType ← Lean.Meta.inferType xs[1]!
          let setType := Lean.mkApp (Lean.mkConst ``Finset [Lean.Level.zero]) columnType
          let membershipType := Lean.mkAppN
            (Lean.mkConst ``Membership [Lean.Level.zero, Lean.Level.zero])
            #[columnType, setType]
          let membership ← Lean.Meta.synthInstance membershipType
          let member := Lean.mkAppN
            (Lean.mkConst ``Membership.mem [Lean.Level.zero, Lean.Level.zero])
            #[columnType, setType, membership, columns, xs[1]!]
          let lhs := Lean.mkAppN terms xs
          let rhs := Lean.mkAppN original xs
          let coefficientType ← Lean.Meta.inferType lhs
          let equal := Lean.mkAppN (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero])
            #[coefficientType, lhs, rhs]
          let value ← Lean.Meta.mkForallFVars xs
            (Lean.Expr.forallE `member member equal Lean.BinderInfo.default)
          -- The original two universal binders, Cartesian membership and
          -- coefficient equality are unchanged. No meta comparison is needed.
          g.assign value
          Lean.Elab.Tactic.replaceMainGoal []

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
  by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let g ← Lean.Elab.Tactic.getMainGoal
        let some rectangles := (← g.getDecl).lctx.findFromUserName? `rectangles
          | throwError "original rectangles local variable not found"
        let terms := Lean.Expr.proj
          ``HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles 1
          (Lean.mkFVar rectangles.fvarId)
        let original ← Lean.Elab.Tactic.elabTerm
          (← `(packet.originalRightRectangle)) none
        let columns ← Lean.Elab.Tactic.elabTerm
          (← `(childCartesianColumns packet.rightReindex.plain₁
            packet.rightReindex.plain₂ packet.rightReindex.slots)) none
        let termsType ← Lean.Meta.inferType terms
        Lean.Meta.forallTelescope termsType fun xs _ => do
          unless xs.size == 2 do
            throwError "original rectangle terms must take comparison and column"
          let columnType ← Lean.Meta.inferType xs[1]!
          let setType := Lean.mkApp (Lean.mkConst ``Finset [Lean.Level.zero]) columnType
          let membershipType := Lean.mkAppN
            (Lean.mkConst ``Membership [Lean.Level.zero, Lean.Level.zero])
            #[columnType, setType]
          let membership ← Lean.Meta.synthInstance membershipType
          let member := Lean.mkAppN
            (Lean.mkConst ``Membership.mem [Lean.Level.zero, Lean.Level.zero])
            #[columnType, setType, membership, columns, xs[1]!]
          let lhs := Lean.mkAppN terms xs
          let rhs := Lean.mkAppN original xs
          let coefficientType ← Lean.Meta.inferType lhs
          let equal := Lean.mkAppN (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero])
            #[coefficientType, lhs, rhs]
          let value ← Lean.Meta.mkForallFVars xs
            (Lean.Expr.forallE `member member equal Lean.BinderInfo.default)
          -- The original two universal binders, Cartesian membership and
          -- coefficient equality are unchanged. No meta comparison is needed.
          g.assign value
          Lean.Elab.Tactic.replaceMainGoal []

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
  by
    run_tac
      Lean.Elab.Tactic.withMainContext do
        let g ← Lean.Elab.Tactic.getMainGoal
        let some rectangles := (← g.getDecl).lctx.findFromUserName? `rectangles
          | throwError "original rectangles local variable not found"
        let rectanglesExpr := Lean.mkFVar rectangles.fvarId
        let leafExpr ← Lean.Elab.Tactic.elabTerm (← `(packet.leaf)) none
        let leafType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType leafExpr)
        IO.eprintln "KDIAG ordinaryBindingProp original leaf type"
        let rectanglesType ← Lean.Meta.withTransparency .all do
          Lean.Meta.whnf (← Lean.Meta.inferType rectanglesExpr)
        IO.eprintln "KDIAG ordinaryBindingProp original rectangles type"
        let typeName := ``HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryBinding
        let info ← Lean.getConstInfo typeName
        let levels := info.levelParams.map (fun _ => Lean.Level.zero)
        let ty := info.type.instantiateLevelParams info.levelParams levels
        Lean.Meta.forallTelescope ty fun xs _ => do
          unless xs.size > 0 do
            throwError "original ordinary binding has no rectangle parameter"
          let rectangleParameter := xs[xs.size - 1]!
          let mut leafParameter : Option Lean.Expr := none
          for x in xs do
            if (← x.fvarId!.getDecl).userName == `leaf then
              leafParameter := some x
          let some leafParameter := leafParameter
            | throwError "original ordinary binding leaf parameter not found"
          let genericLeafType ← Lean.Meta.withTransparency .all do
            Lean.Meta.whnf (← Lean.Meta.inferType leafParameter)
          let genericRectanglesType ← Lean.Meta.withTransparency .all do
            Lean.Meta.whnf (← Lean.Meta.inferType rectangleParameter)
          let mut bindings : Array (Lean.Expr × Lean.Expr) := #[]
          for (template, actual) in
              #[(genericLeafType, leafType), (genericRectanglesType, rectanglesType)] do
            unless template.getAppFn == actual.getAppFn do
              throwError "original ordinary binding input type head changed"
            let genericArgs := template.getAppArgs
            let actualArgs := actual.getAppArgs
            unless genericArgs.size == actualArgs.size do
              throwError "original ordinary binding input type arity changed"
            for i in [:genericArgs.size] do
              let parameter := genericArgs[i]!
              if parameter.isFVar then
                if !(bindings.any (fun p => p.1 == parameter)) then
                  bindings := bindings.push (parameter, actualArgs[i]!)
              -- In particular the product-space instance and the two slot
              -- projections are derived expressions, checked by the kernel.
          let mut args : Array Lean.Expr := #[]
          for i in [:xs.size] do
            let x := xs[i]!
            let d ← x.fvarId!.getDecl
            let actualType := d.type.replaceFVars (xs.extract 0 i) args
            let arg ←
              if x == leafParameter then
                pure leafExpr
              else if x == rectangleParameter then
                pure rectanglesExpr
              else
                match bindings.find? (fun p => p.1 == x) with
                | some pair => pure pair.2
                | none =>
                  if d.binderInfo == Lean.BinderInfo.instImplicit then
                    Lean.Meta.synthInstance actualType
                  else
                    throwError "unmapped original ordinary binding parameter {d.userName}"
            args := args.push arg
          IO.eprintln "KDIAG ordinaryBindingProp original parameter spine reconstructed"
          -- The same original leaf and original rectangles are supplied to
          -- the original proposition constant; normal kernel checking remains.
          g.assign (Lean.mkAppN (Lean.mkConst typeName levels) args)
          Lean.Elab.Tactic.replaceMainGoal []

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
