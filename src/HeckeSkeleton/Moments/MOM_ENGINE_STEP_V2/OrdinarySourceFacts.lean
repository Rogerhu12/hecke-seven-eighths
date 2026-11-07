module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original source facts used by the four ordinary rectangles

Every fact below is inherited from the same realized raw packet. The
actual common class is active, so its coefficient gate can be opened;
the two original rectangles retain the same linear column multiplier.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PhysicalSource

variable (source : PhysicalSource call p)

/-- The actual comparison bit is applied to both original rectangles
before either transform, including the uncentered zero rectangle. -/
theorem rectangle_sub (i : source.Column) :
    source.rectangle false i - source.rectangle true i =
      source.multiplier i *
        call.workingValues.coefficient call.node.centered (source.ancestor i) := by
  cases hc : call.node.centered <;>
    simp only [rectangle, hc, Bool.false_eq_true, if_false, if_true,
      ParentRawAtoms.ConstantValues.coefficient, sub_zero, mul_sub]

end PhysicalSource

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem realizes_second (hpacket : packet.Realizes) : packet.second.Realizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact htrace.second.stage (raw.index j).val.1.1

theorem realizes_activeCommon (hpacket : packet.Realizes) :
    packet.key.1.val ∈ packet.second.physical.activeCommon := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (raw.active j).2.2.1

theorem realizes_liveRows (hpacket : packet.Realizes) : packet.R.live.Nonempty := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (raw.active j).2.2.2

/-- Multiplication by the second norm tilt and divisor phase is the
same on the two original comparison rectangles. -/
theorem originalLeftRectangle_sub
    (i : AllocationColumn K packet.leaf.leftSlots) :
    packet.originalLeftRectangle false i - packet.originalLeftRectangle true i =
      (packet.second.physical.multiplier (packet.leftReindex.index i) *
        call.workingValues.coefficient call.node.centered
          (packet.second.physical.ancestor (packet.leftReindex.index i))) *
        packet.leftSecondMultiplier (packet.leftReindex.index i) := by
  rw [originalLeftRectangle, originalLeftRectangle, ← sub_mul,
    packet.second.physical.rectangle_sub]

theorem originalRightRectangle_sub
    (i : AllocationColumn K packet.leaf.rightSlots) :
    packet.originalRightRectangle false i - packet.originalRightRectangle true i =
      (packet.second.physical.multiplier (packet.rightReindex.index i) *
        call.workingValues.coefficient call.node.centered
          (packet.second.physical.ancestor (packet.rightReindex.index i))) *
        packet.rightSecondMultiplier (packet.rightReindex.index i) := by
  rw [originalRightRectangle, originalRightRectangle, ← sub_mul,
    packet.second.physical.rectangle_sub]

/-- The active common-class gate is removed using the original S4
realization; no inactive rectangle is silently retained. -/
theorem leftWhole_eq_source (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.leftSlots) :
    packet.leftWhole i =
      packet.second.physical.source.coefficient (packet.leftReindex.index i) *
        packet.leftSecondMultiplier (packet.leftReindex.index i) := by
  change packet.chart.sourceLeftCoefficient (packet.leftReindex.index i) = _
  rw [SecondBlockProfileChart.sourceLeftCoefficient,
    (packet.realizes_second hpacket).leftCoefficient,
    if_pos (packet.realizes_activeCommon hpacket)]
  simp only [leftSecondMultiplier]
  ring

theorem rightWhole_eq_source (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.rightSlots) :
    packet.rightWhole i =
      packet.second.physical.source.coefficient (packet.rightReindex.index i) *
        packet.rightSecondMultiplier (packet.rightReindex.index i) := by
  change packet.chart.sourceRightCoefficient (packet.rightReindex.index i) = _
  rw [SecondBlockProfileChart.sourceRightCoefficient,
    (packet.realizes_second hpacket).rightCoefficient,
    if_pos (packet.realizes_activeCommon hpacket)]
  simp only [rightSecondMultiplier]
  ring

theorem leftWhole_eq_rectangle_sub (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.leftSlots)
    (hsource : packet.second.physical.source.coefficient (packet.leftReindex.index i) =
      packet.second.physical.multiplier (packet.leftReindex.index i) *
        call.workingValues.coefficient call.node.centered
          (packet.second.physical.ancestor (packet.leftReindex.index i))) :
    packet.leftWhole i =
      packet.originalLeftRectangle false i - packet.originalLeftRectangle true i := by
  rw [packet.leftWhole_eq_source hpacket, packet.originalLeftRectangle_sub, hsource]

theorem rightWhole_eq_rectangle_sub (hpacket : packet.Realizes)
    (i : AllocationColumn K packet.leaf.rightSlots)
    (hsource : packet.second.physical.source.coefficient (packet.rightReindex.index i) =
      packet.second.physical.multiplier (packet.rightReindex.index i) *
        call.workingValues.coefficient call.node.centered
          (packet.second.physical.ancestor (packet.rightReindex.index i))) :
    packet.rightWhole i =
      packet.originalRightRectangle false i - packet.originalRightRectangle true i := by
  rw [packet.rightWhole_eq_source hpacket, packet.originalRightRectangle_sub, hsource]

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.realizes_second
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.leftWhole_eq_rectangle_sub
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.rightWhole_eq_rectangle_sub
