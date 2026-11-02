import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawLeafData
import Lean

set_option stderrAsMessages false
set_option linter.unusedSectionVars false
set_option Elab.async false
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


run_meta do
  let names : Array Name := #[
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.chart,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.rowLabel,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SourceClassKey.rawLeaf,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.chart,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.block,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.R,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.secondSourceLeafLive,
  `HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondSource.stage,
  `HeckeSkeleton.Moments.EngineStep.ActualGaussStage.charts,
  `HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.rowLabelCount,
  `HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows,
  `HeckeSkeleton.Moments.EngineStep.SourceCartesianCover.branch,
  `HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.branch,
  `HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.residualReindex,
  `HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.plain₁,
  `HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.plain₂,
  `HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.slots,
  `HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.index
]
  for n in names do
    if let some info := (← getEnv).find? n then
      IO.eprintln s!"KDIAG_TYPE {n}: depth {info.type.approxDepth}"
    else IO.eprintln s!"KDIAG_MISSING {n}"
  (← IO.getStderr).flush
  for n in names do
    kdiagTime n
