import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridOrdinaryProduction
import Lean

set_option stderrAsMessages false
open Lean Meta

def kdiagTime (n : Name) : MetaM Unit := do
  let some info := (← getEnv).find? n | IO.eprintln s!"KDIAG missing {n}"
  let f := mkConst n (info.levelParams.map mkLevelParam)
  let ty := info.type
  let t0 ← IO.monoMsNow
  let arity ← forallTelescopeReducing ty fun xs _ => pure xs.size
  IO.eprintln s!"KDIAG {n}: arity {arity}, type size {ty.approxDepth}"
  (← IO.getStderr).flush
  let _ ← getFunInfo f
  IO.eprintln s!"KDIAG {n}: getFunInfo {(← IO.monoMsNow) - t0} ms"
  (← IO.getStderr).flush

run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.R
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.chart
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.block
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.leftReindex
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.rightReindex
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.chart
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.leftFrame
run_meta kdiagTime `HeckeSkeleton.Moments.EngineStep.HybridOrdinaryRectangles.rightFrame
