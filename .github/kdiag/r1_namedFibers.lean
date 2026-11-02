import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GeometryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData
import Lean.Elab.Command

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: imports"
    stderr.flush

/-!
# S6: the original finite cover, two divisors and live hybrid leaves

A cover's label is the actual original occurrence-extraction tuple.
Its Cartesian dictionary reconstructs the same original column. The
finite family then enumerates every live actual covered allocation key
exactly once. In particular neither copying a leaf nor increasing an
outer multiplier preserves this contract.

The exceptional predicate is computed from the original moving list,
the actual first/pool phases and the actual extracted second row. It
is tested in the unchanged parent theta set before the two centered
rectangles are separated. Paper: Section 4.8, lines 2908--2925.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  coveredClassKeyFintype

local instance rawContractsCircleFintype : Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) :=
  Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: before OriginalCover"
    stderr.flush

set_option genInjectivity false in
set_option genSizeOf false in
/-- Only original occurrence tuples can label a source cover. -/
structure OriginalCover (source : PhysicalSource call p) where
  cover : SourceCartesianCover source.source.columns source.source.ideal
  label : cover.Label ↪ SupportCartesian.ExtractionKey K call.localizedData.geometry.slotCount
  first : ∀ a : cover.labels,
    SupportCartesianBranch call.workingRaw.originalPlain₁
      call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots source.first.fullDeletion

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after OriginalCover"
    stderr.flush

namespace OriginalCover

variable {source : PhysicalSource call p} (cover : OriginalCover source)

structure Realizes : Prop where
  labels : ∀ a : cover.cover.labels, ∃ i ∈ source.source.columns, cover.cover.label i = a.val
  label : ∀ i ∈ source.source.columns, cover.label (cover.cover.label i) =
    call.workingRaw.originalReindex.supportExtractionLabel source.first.fullDeletion
      (source.ancestor i)
  first : ∀ a, (cover.first a).key = cover.label a.val
  count : ∀ a, (cover.first a).keep.card = (cover.cover.branch a).slotCount
  plain₁ : ∀ a, (cover.cover.branch a).reindex.plain₁ =
    SupportCartesian.plainResidual call.workingRaw.originalPlain₁
      source.first.fullDeletion (cover.first a).plainExtract₁
  plain₂ : ∀ a, (cover.cover.branch a).reindex.plain₂ =
    SupportCartesian.plainResidual call.workingRaw.originalPlain₂
      source.first.fullDeletion (cover.first a).plainExtract₂
  slots : ∀ a, HEq (cover.cover.branch a).reindex.slots
    (fun j : Fin (cover.first a).keep.card =>
      SupportCartesian.primeLive
        (call.workingRaw.exteriorSlots (SlotRestriction.index (cover.first a).keep j))
        source.first.fullDeletion)
  index : ∀ a (x : AllocationColumn K (cover.first a).keep.card),
    x ∈ (cover.first a).residualColumns →
    source.ancestor ((cover.cover.branch a).reindex.index
      (cast (congrArg (AllocationColumn K) (count a)) x)) =
      call.workingRaw.originalIndex ((cover.first a).reconstruct x)

end OriginalCover

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after OriginalCover.Realizes"
    stderr.flush

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family}

set_option genInjectivity false in
set_option genSizeOf false in
structure RawCovers (second : SecondFamily expansion) where
  left : ∀ i, OriginalCover (second.source i).physical
  right : ∀ i, OriginalCover (second.source i).physical

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after RawCovers"
    stderr.flush

namespace RawCovers

variable {second : SecondFamily expansion} (covers : RawCovers second)

def predicates (i : Fin expansion.count) :
    ActualGaussStage.CoverHybridPredicates.{0, 0, 0, 0}
      (second.source i).stage (covers.left i).cover (covers.right i).cover :=
  fun DE D _ _ label _ _ _ _ _ _ h =>
    (second.source i).rowCharacter (expansion := expansion) i DE D label h ∈ call.node.data.theta

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after predicates"
    stderr.flush


/-- The class keys of one source, under a short name so that a Sigma over the
sources does not carry the whole `SourceClassKey` telescope in its fibre. -/
def ClassFiber (i : Fin expansion.count) : Type :=
  SourceClassKey (second.source i).stage (covers.left i).cover (covers.right i).cover

instance classFiberFintype (i : Fin expansion.count) : Fintype (covers.ClassFiber i) :=
  inferInstanceAs (Fintype (SourceClassKey _ _ _))

abbrev ClassKey := Σ i : Fin expansion.count, covers.ClassFiber i


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r ClassKey done"
    stderr.flush

def AllocationFiber (key : covers.ClassKey) : Type :=
  SourceClassKey.AllocationKey (s := (second.source key.1).stage)
    (LC := (covers.left key.1).cover) (RC := (covers.right key.1).cover)
    (show SourceClassKey (second.source key.1).stage (covers.left key.1).cover
      (covers.right key.1).cover from key.2)

instance allocationFiberFintype (key : covers.ClassKey) : Fintype (covers.AllocationFiber key) :=
  inferInstanceAs (Fintype (SourceClassKey.AllocationKey _))

abbrev Key := Σ key : covers.ClassKey, covers.AllocationFiber key


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r Key done"
    stderr.flush

example : Fintype covers.Key := inferInstance


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r Fintype done"
    stderr.flush

noncomputable def leafAt (i : Fin expansion.count)
    (v : SourceClassKey (second.source i).stage (covers.left i).cover (covers.right i).cover)
    (allocation : SourceClassKey.AllocationKey v) :
    ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  secondSourceLeaf (K := K) (c := c) (call := call) (p := p)
    (second.source i) (covers.left i).cover (covers.right i).cover v
    (RawCovers.predicates
      (K := K) (c := c) (call := call) (p := p)
      (F := F) (family := family) (expansion := expansion)
      (second := second) covers i)
    allocation

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r leafAt done"
    stderr.flush


noncomputable def leaf (key : covers.Key) : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  covers.leafAt key.1.1 key.1.2 key.2


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r leaf projections done"
    stderr.flush

noncomputable def leafMatch (key : covers.Key) : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  match key with
  | ⟨⟨i, v⟩, allocation⟩ => covers.leafAt i v allocation


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r leaf match done"
    stderr.flush

noncomputable example (i : Fin expansion.count)
    (v : SourceClassKey (second.source i).stage (covers.left i).cover (covers.right i).cover)
    (a : SourceClassKey.AllocationKey v) : covers.Key :=
  ⟨⟨i, v⟩, a⟩


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r mk done"
    stderr.flush

def classKey (key : covers.Key) : SecondClassKey second where
  sourceIndex := key.1.1
  common := key.1.2.1
  divisor := key.1.2.2.1
  rowLabel := SourceClassKey.rowLabel (show SourceClassKey (second.source key.1.1).stage
    (covers.left key.1.1).cover (covers.right key.1.1).cover from key.1.2)


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r classKey done"
    stderr.flush

abbrev LiveKey := {key : covers.Key //
  (covers.leaf key).Live ∧ (covers.classKey key).Active}

example : Fintype covers.LiveKey := inferInstance

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG r1_namedFibers done"
    stderr.flush

end RawCovers
