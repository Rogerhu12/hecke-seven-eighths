import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.GeometryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawRectangleData

set_option linter.unusedSectionVars false
set_option autoImplicit false

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

/-- Only original occurrence tuples can label a source cover. -/
structure OriginalCover (source : PhysicalSource call p) where
  cover : SourceCartesianCover source.source.columns source.source.ideal
  label : cover.Label ↪ SupportCartesian.ExtractionKey K call.localizedData.geometry.slotCount
  first : ∀ a : cover.labels,
    SupportCartesianBranch call.workingRaw.originalPlain₁
      call.workingRaw.originalPlain₂ call.workingRaw.exteriorSlots source.first.fullDeletion

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

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family}

structure RawCovers (second : SecondFamily expansion) where
  left : ∀ i, OriginalCover (second.source i).physical
  right : ∀ i, OriginalCover (second.source i).physical

namespace RawCovers

variable {second : SecondFamily expansion} (covers : RawCovers second)

def predicates (i : Fin expansion.count) :
    (second.source i).stage.CoverHybridPredicates (covers.left i).cover (covers.right i).cover :=
  fun DE D _ _ label _ _ _ _ _ _ h =>
    (second.source i).rowCharacter (expansion := expansion) i DE D label h ∈ call.node.data.theta

abbrev ClassKey := Σ i : Fin expansion.count,
  SourceClassKey (second.source i).stage (covers.left i).cover (covers.right i).cover

abbrev Key := Σ key : covers.ClassKey, SourceClassKey.AllocationKey key.2

def classKey (key : covers.Key) : SecondClassKey second where
  sourceIndex := key.1.1
  common := key.1.2.1
  divisor := key.1.2.2.1
  rowLabel := SourceClassKey.rowLabel key.1.2

def leaf (key : covers.Key) : ActualHybridLeaf K (Arithmetic.Orbit c) ℝ ℝ :=
  secondSourceLeaf (second.source key.1.1) (covers.left key.1.1).cover
    (covers.right key.1.1).cover key.1.2 (covers.predicates key.1.1) key.2

/-- Zero physical sources and classes with identically zero complete
correlation are removed as well as zero whole-column leaves. The S6
proof must show that each removed class has both costs zero. -/
abbrev LiveKey := {key : covers.Key //
  (covers.leaf key).Live ∧ (covers.classKey key).Active}

end RawCovers

/-- No leaf is chosen independently. Packets are computed from the
exact live key, its original first branches and its S5 geometry. -/
structure RawFamily {second : SecondFamily expansion} (geometry : GeometryFamily second) where
  covers : RawCovers second
  count : ℕ
  index : Fin count ≃ covers.LiveKey

namespace RawFamily

variable {second : SecondFamily expansion} {geometry : GeometryFamily second}
variable (raw : RawFamily geometry)

theorem active (j : Fin raw.count) :
    (raw.covers.classKey (raw.index j).val).Active :=
  (raw.index j).property.2

def packet (j : Fin raw.count) : RawLeafPacket call p :=
  let key := (raw.index j).val
  { second := second.source key.1.1
    leftCover := (raw.covers.left key.1.1).cover
    rightCover := (raw.covers.right key.1.1).cover
    key := key.1.2
    exceptional := raw.covers.predicates key.1.1
    allocation := key.2
    physicalRows := (raw.active j).2.1
    live := (raw.index j).property.1
    nominal := (geometry.geometry (raw.covers.classKey key) (raw.active j)).nominal
    leftFirst := (raw.covers.left key.1.1).first key.1.2.2.2.1
    rightFirst := (raw.covers.right key.1.1).first key.1.2.2.2.2.1 }

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

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
