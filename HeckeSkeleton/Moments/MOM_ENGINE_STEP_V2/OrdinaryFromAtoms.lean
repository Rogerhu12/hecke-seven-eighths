import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRawAtomData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryLeafLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySourceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOriginalCoordinates

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual ordinary seed from its individual original atom identities

This assembly uses the original divisor allocation, original whole
coefficients and genuine row translations. Every field of the global
atom binding is computed from the same original table. The only input
identities left to the coefficient calculation are the two single
Cartesian-column rectangle identities.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem allocated_mem_cartesian {k : ℕ}
    (D : Ideal (𝓞 K))
    (a : HeckePort.IdealMobiusDivisorSum.primeSupport D → Finset (Fin (k + 2)))
    (S₁ S₂ : Finset (Ideal (𝓞 K)))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (i : AllocationColumn K k)
    (hi : i ∈ pairedAllocatedColumns D a S₁ S₂ S id id HeightOneSpectrum.asIdeal) :
    i ∈ childCartesianColumns S₁ S₂ S := by
  rw [paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def atomLeftPoint (_h : Arithmetic.Orbit c) :
    AllocationColumn K packet.leaf.leftSlots → EngineParameter :=
  rawSourceLocation (CanonicalLiteralLocations.plain packet.firstSign)
    (CanonicalLiteralLocations.plain packet.firstSign)
    (CanonicalLiteralLocations.prime packet.firstSign)

def atomRightPoint (_h : Arithmetic.Orbit c) :
    AllocationColumn K packet.leaf.rightSlots → EngineParameter :=
  rawSourceLocation (CanonicalLiteralLocations.plain (-packet.firstSign))
    (CanonicalLiteralLocations.plain (-packet.firstSign))
    (CanonicalLiteralLocations.prime (-packet.firstSign))

theorem leftAllocated_cartesian (i : AllocationColumn K packet.leaf.leftSlots)
    (hi : i ∈ packet.leaf.left) : i ∈ packet.leftReindex.cartesian := by
  exact allocated_mem_cartesian packet.allocation.1.val packet.allocation.2.2.1.val
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots i hi

theorem rightAllocated_cartesian (i : AllocationColumn K packet.leaf.rightSlots)
    (hi : i ∈ packet.leaf.right) : i ∈ packet.rightReindex.cartesian := by
  exact allocated_mem_cartesian packet.allocation.1.val packet.allocation.2.2.2.val
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots i hi

variable (hpacket : packet.Realizes) (phases : OriginalPhaseData packet)
variable (hleft : ∀ r i, i ∈ packet.leftReindex.cartesian →
  (packet.beforeAtomTable hpacket phases false).term r i = packet.originalLeftRectangle r i)
variable (hright : ∀ r i, i ∈ packet.rightReindex.cartesian →
  (packet.beforeAtomTable hpacket phases true).term r i = packet.originalRightRectangle r i)

def atomRectangles : HybridOrdinaryRectangles packet.R PUnit
    packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
    packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
    packet.leftIdeal packet.rightIdeal (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    packet.leftWhole packet.rightWhole packet.atomLeftPoint packet.atomRightPoint
    packet.ordinaryAllocation packet.leaf.exceptional where
  leftTerms := (packet.beforeAtomTable hpacket phases false).term
  rightTerms := (packet.beforeAtomTable hpacket phases true).term
  left_difference i hi := by
    have hc := packet.leftAllocated_cartesian i hi
    rw [hleft false i hc, hleft true i hc]
    exact packet.leftWhole_eq_rectangle_sub hpacket i (packet.realizes_coefficient hpacket _)
  right_difference i hi := by
    have hc := packet.rightAllocated_cartesian i hi
    rw [hright false i hc, hright true i hc]
    exact packet.rightWhole_eq_rectangle_sub hpacket i (packet.realizes_coefficient hpacket _)
  leftFactors r :=
    (packet.beforeAtomTable hpacket phases false).factors
      (packet.R.restrictRows (fun h => ¬packet.leaf.exceptional h)) .left
      packet.ordinaryAllocation.val.2.1
      packet.leftReindex.plain₁ packet.leftReindex.plain₂ packet.leftReindex.slots
      packet.leftReindex_plain₁_ne_zero packet.leftReindex_plain₂_ne_zero
      packet.leftIdeal packet.leftReindex.ideal_product packet.firstSign r
  rightFactors r :=
    (packet.beforeAtomTable hpacket phases true).factors
      (packet.R.restrictRows (fun h => ¬packet.leaf.exceptional h)) .right
      packet.ordinaryAllocation.val.2.1
      packet.rightReindex.plain₁ packet.rightReindex.plain₂ packet.rightReindex.slots
      packet.rightReindex_plain₁_ne_zero packet.rightReindex_plain₂_ne_zero
      packet.rightIdeal packet.rightReindex.ideal_product (-packet.firstSign) r

def atomOrdinaryData : OrdinaryData packet :=
  packet.ordinaryDataOfTranslatedRectangles packet.atomLeftPoint packet.atomRightPoint
    (packet.atomRectangles hpacket phases hleft hright) hleft hright
    (fun h _ => ⟨packet.leftRowTranslation h, fun i hi =>
      packet.ordinaryLeftPoint_eq_translation hpacket h i (packet.leftAllocated_cartesian i hi)⟩)
    (fun h _ => ⟨packet.rightRowTranslation h, fun i hi =>
      packet.ordinaryRightPoint_eq_translation hpacket h i (packet.rightAllocated_cartesian i hi)⟩)

def atomBinding :
    OriginalAtomBinding (packet.atomOrdinaryData hpacket phases hleft hright) phases
      (packet.ordinaryOccurrences hpacket (packet.atomOrdinaryData hpacket phases hleft hright)) where
  base side r := by cases side <;> rfl
  scale₁ side r := by cases side <;> rfl
  scale₂ side r := by cases side <;> rfl
  length side r i := by cases side <;> rfl
  characters side r h := by cases side <;> rfl
  leftWeight side r h I := by
    cases side <;>
      exact packet.beforeAtomTable_comparisonWeight hpacket
        (packet.atomOrdinaryData hpacket phases hleft hright) phases _ r I
  rightWeight side r h I := by
    cases side with
    | false =>
        exact packet.beforeAtomTable_rightWeight hpacket
          (packet.atomOrdinaryData hpacket phases hleft hright) phases false r I
    | true =>
        exact packet.beforeAtomTable_rightWeight hpacket
          (packet.atomOrdinaryData hpacket phases hleft hright) phases true r I
  slotWeight side r h i q := by cases side <;> rfl
  leftLocation side r h I := by cases side <;> rfl
  rightLocation side r h I := by cases side <;> rfl
  slotLocation side r h i q := by cases side <;> rfl
  gaussNormalizer side r := by
    cases side <;> exact packet.beforeAtomTable_normalizer hpacket phases _

/-- Full seed assembly, including the same original global fields and
the same exact independent allocation. -/
def atomSeed : OrdinarySeed packet where
  ordinary := packet.atomOrdinaryData hpacket phases hleft hright
  phases := phases
  occurrences := packet.ordinaryOccurrences hpacket
    (packet.atomOrdinaryData hpacket phases hleft hright)
  atoms := packet.atomBinding hpacket phases hleft hright
  reference := packet.originalReference hpacket
  reference_mem := packet.originalReference_mem hpacket
  plain_scales side r plain := by cases side <;> cases plain <;> rfl
  residual_count side := by cases side <;> rfl
  lengths side i := by cases side <;> rfl

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.atomOrdinaryData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.atomBinding
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.atomSeed
