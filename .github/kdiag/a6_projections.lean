import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import Lean

set_option linter.unusedSectionVars false
set_option stderrAsMessages false
set_option Elab.async false
open Lean Meta

def kdiagProjectionTime (n : Name) (field : Nat) : MetaM Unit := do
  let some info := (← getEnv).find? n | IO.eprintln s!"KDIAG missing {n}"
  let f := mkConst n (info.levelParams.map mkLevelParam)
  forallTelescopeReducing info.type fun xs _ => do
    let projection := mkProj `HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex field
      (mkAppN f xs)
    let ty ← inferType projection
    IO.eprintln s!"KDIAG_PROJ {n} field={field}: depth {ty.approxDepth}"
    (← IO.getStderr).flush
    let start ← IO.monoMsNow
    let _ ← getFunInfo projection
    IO.eprintln s!"KDIAG_PROJ {n} field={field}: {(← IO.monoMsNow) - start} ms"
    (← IO.getStderr).flush

run_meta kdiagProjectionTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.rightReindex 3
run_meta kdiagProjectionTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.rightReindex 2
run_meta kdiagProjectionTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.leftReindex 3
run_meta kdiagProjectionTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.leftReindex 2
