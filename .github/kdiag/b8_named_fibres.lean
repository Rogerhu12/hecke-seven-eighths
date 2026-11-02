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

/- Insert before RawCovers's concrete declarations, inside Blueprint. -/
universe uI uV uA

set_option genInjectivity false in
set_option genSizeOf false in
structure RawDependentKey (I : Type uI) (V : I → Type uV)
    (A : (i : I) → V i → Type uA) where
  i : I
  v : V i
  allocation : A i v

namespace RawDependentKey

variable {I : Type uI} {V : I → Type uV} {A : (i : I) → V i → Type uA}

/-- This equivalence is elaborated for abstract families, before specialization. -/
def sigmaEquiv : RawDependentKey I V A ≃ (Σ i : I, Σ v : V i, A i v) where
  toFun key := ⟨key.i, key.v, key.allocation⟩
  invFun key := ⟨key.1, key.2.1, key.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The precise old RawCovers.Key layout, proved abstractly as well. -/
def pairEquiv : RawDependentKey I V A ≃ (Σ key : Sigma V, A key.1 key.2) where
  toFun key := ⟨⟨key.i, key.v⟩, key.allocation⟩
  invFun key := ⟨key.1.1, key.1.2, key.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Register only locally where this finite enumeration is needed. -/
def fintype [Fintype I] [∀ i, Fintype (V i)] [∀ i v, Fintype (A i v)] :
    Fintype (RawDependentKey I V A) :=
  Fintype.ofEquiv (Σ i : I, Σ v : V i, A i v) sigmaEquiv.symm

end RawDependentKey


run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG B generic key and equivalences ready"
    stderr.flush

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

abbrev ClassKey := Σ i : Fin expansion.count,
  SourceClassKey (second.source i).stage (covers.left i).cover (covers.right i).cover

/-- Named fibres keep dependent projections at this short interface. -/
def ClassAt (i : Fin expansion.count) : Type :=
  SourceClassKey (second.source i).stage
    (covers.left i).cover (covers.right i).cover

def AllocationAt (i : Fin expansion.count) (v : covers.ClassAt i) : Type :=
  SourceClassKey.AllocationKey
    (s := (second.source i).stage)
    (LC := (covers.left i).cover) (RC := (covers.right i).cover) v

noncomputable def classAtFintype (i : Fin expansion.count) :
    Fintype (covers.ClassAt i) := by
  unfold ClassAt
  infer_instance

noncomputable def allocationAtFintype (i : Fin expansion.count)
    (v : covers.ClassAt i) : Fintype (covers.AllocationAt i v) := by
  unfold AllocationAt
  infer_instance

attribute [local instance] classAtFintype allocationAtFintype

abbrev KeyS := RawDependentKey (Fin expansion.count)
  covers.ClassAt covers.AllocationAt

abbrev Key := covers.KeyS

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after ClassKey and Key"
    stderr.flush

def classKey (key : covers.Key) : SecondClassKey second where
  sourceIndex := key.i
  common := key.v.1
  divisor := key.v.2.1
  rowLabel := SourceClassKey.rowLabel key.v

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after classKey"
    stderr.flush

noncomputable def leafAt (i : Fin expansion.count)
    (v : covers.ClassAt i)
    (allocation : covers.AllocationAt i v) :
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
    stderr.putStrLn "KDIAG B leafAt ready"
    stderr.flush

noncomputable def leaf (key : covers.Key) : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  covers.leafAt key.i key.v key.allocation

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after leaf"
    stderr.flush

/-- Zero physical sources and classes with identically zero complete
correlation are removed as well as zero whole-column leaves. The S6
proof must show that each removed class has both costs zero. -/
abbrev LiveKey := {key : covers.Key //
  (covers.leaf key).Live ∧ (covers.classKey key).Active}

noncomputable def keySFintype : Fintype covers.KeyS :=
  RawDependentKey.fintype

attribute [local instance] keySFintype

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG B KeyS Fintype ready"
    stderr.flush

noncomputable def liveKeyFintype : Fintype covers.LiveKey := inferInstance

attribute [local instance] liveKeyFintype

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "KDIAG B LiveKey Fintype ready"
    stderr.flush


end RawCovers

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after LiveKey"
    stderr.flush

set_option diagnostics true in
set_option genInjectivity false in
set_option genSizeOf false in
/-- No leaf is chosen independently. Packets are computed from the
exact live key, its original first branches and its S5 geometry. -/
structure RawFamily {second : SecondFamily expansion} (geometry : GeometryFamily second) where
  covers : RawCovers second
  count : ℕ
  index : Fin count ≃ covers.LiveKey

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after RawFamily"
    stderr.flush

namespace RawFamily

variable {second : SecondFamily expansion} {geometry : GeometryFamily second}
variable (raw : RawFamily geometry)

theorem active (j : Fin raw.count) :
    (raw.covers.classKey (raw.index j).val).Active :=
  (raw.index j).property.2

def packet (j : Fin raw.count) : RawLeafPacket call p :=
  let key := (raw.index j).val
  { second := second.source key.i
    leftCover := (raw.covers.left key.i).cover
    rightCover := (raw.covers.right key.i).cover
    key := key.v
    exceptional := raw.covers.predicates key.i
    allocation := key.allocation
    physicalRows := (raw.active j).2.1
    live := (raw.index j).property.1
    nominal := (geometry.geometry (raw.covers.classKey key) (raw.active j)).nominal
    leftFirst := (raw.covers.left key.i).first key.v.2.2.1
    rightFirst := (raw.covers.right key.i).first key.v.2.2.2.1 }

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: after packet"
    stderr.flush

def Realizes : Prop := ∀ i, (raw.covers.left i).Realizes ∧ (raw.covers.right i).Realizes

def exceptional : ℝ := ∑ j, (raw.packet j).leaf.exceptionalCost
def ordinary : ℝ := ∑ j, (raw.packet j).leaf.ordinaryCost
def normalizedExceptional : ℝ := call.normalizedScalar raw.exceptional
def normalizedOrdinary : ℝ := call.normalizedScalar raw.ordinary

theorem normalizedExceptional_nonneg : 0 ≤ raw.normalizedExceptional :=
  call.normalizedScalar_nonneg
    (Finset.sum_nonneg (fun j _ => (raw.packet j).leaf.exceptionalCost_nonneg))

theorem normalizedOrdinary_nonneg : 0 ≤ raw.normalizedOrdinary :=
  call.normalizedScalar_nonneg
    (Finset.sum_nonneg (fun j _ => (raw.packet j).leaf.ordinaryCost_nonneg))

end RawFamily

namespace RawLeafPacket

/-- Later single-leaf tasks quantify only over packets from the same
fully specified original source chain. This carries no parent, mass,
terminal, capacity or descendant estimate. -/
def Realizes (packet : RawLeafPacket call p) : Prop :=
  ∃ trace : SourceTrace call p, ∃ geometry : GeometryFamily trace.second,
    ∃ raw : RawFamily geometry, ∃ j : Fin raw.count,
      trace.Realizes ∧ geometry.Realizes ∧ raw.Realizes ∧ raw.packet j = packet

end RawLeafPacket

namespace RawFamily

theorem packet_realizes (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) (j : Fin raw.count) :
    (raw.packet j).Realizes :=
  ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩

end RawFamily

/-- S6. Exact original finite covers, both independent divisors,
their occurrence allocations, and the whole exceptional/ordinary split.
The proof removes an inactive class only after proving its original
whole-source coefficient or complete correlation is identically zero. -/
def FiniteLeafTask (c : TargetContext K) (p : SourceParameters c) : Prop :=
  ∀ (call : Call c) (trace : SourceTrace call p), trace.Realizes →
    ∀ geometry : GeometryFamily trace.second, geometry.Realizes →
      ∃ raw : RawFamily geometry, raw.Realizes ∧
        trace.second.nonzero ≤ raw.exceptional + raw.ordinary

run_cmd do
  Lean.Elab.Command.liftIO do
    let stderr ← IO.getStderr
    stderr.putStrLn "MOM_ENGINE_STEP_V2 RawContracts checkpoint: complete"
    stderr.flush

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawDependentKey.sigmaEquiv
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawDependentKey.pairEquiv
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawDependentKey.fintype
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawCovers.leafAt
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawCovers.leaf
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.packet
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.packet_realizes
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FiniteLeafTask
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawCovers.keySFintype
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawCovers.liveKeyFintype
