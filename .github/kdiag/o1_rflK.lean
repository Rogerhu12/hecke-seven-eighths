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

noncomputable def rightIdeal' := fun i => packet.block.rightResidual (packet.rightReindex.index i)


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG o ideal done"
    stderr.flush

example : SourceClassKey.AllocationKey (s := packet.second.stage) (LC := packet.leftCover)
      (RC := packet.rightCover) packet.key =
    SecondAllocationBranch (A := Arithmetic.data c) PUnit.{1}
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.rightIdeal' (SourceClassKey.leftSlots packet.key) := rfl

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG o1_rflK done"
    stderr.flush

end RawLeafPacket
