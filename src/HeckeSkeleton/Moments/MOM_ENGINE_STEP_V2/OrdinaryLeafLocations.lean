module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryPointTransport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySourceFacts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryLeafBinding

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual two Fourier locations and their common row translations

Both coordinates come from the same original source column. The
fixed pool power and the complete extracted second ideal contribute
only a common row translation. Every residual plain and prime
occurrence retains its actual signed logarithm.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem leftReindex_mem_common (i : AllocationColumn K packet.leaf.leftSlots)
    (hi : i ∈ packet.leftReindex.cartesian) :
    packet.leftReindex.index i ∈ packet.block.leftColumns packet.second.physical.source.columns := by
  have hm := packet.leftReindex.maps i hi
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc.1).1, hc.2⟩

theorem rightReindex_mem_common (i : AllocationColumn K packet.leaf.rightSlots)
    (hi : i ∈ packet.rightReindex.cartesian) :
    packet.rightReindex.index i ∈ packet.block.rightColumns packet.second.physical.source.columns := by
  have hm := packet.rightReindex.maps i hi
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc.1).1, hc.2⟩

def leftRowTranslation (h : Arithmetic.Orbit c) : EngineParameter :=
  WithLp.toLp 2
    (-packet.firstSign * Real.log
      ((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower *
        (Arithmetic.data c).exteriorNorm packet.block.commonLeftIdeal),
      Real.log (CanonicalSecondLogChart.rowRadius packet.second.stage.radius packet.key.2.1.val h).val -
        Real.log ((Arithmetic.data c).exteriorNorm packet.block.commonLeftIdeal))

def rightRowTranslation (_h : Arithmetic.Orbit c) : EngineParameter :=
  WithLp.toLp 2
    (packet.firstSign * Real.log
      ((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower *
        (Arithmetic.data c).exteriorNorm packet.block.commonRightIdeal),
      -Real.log ((Arithmetic.data c).exteriorNorm packet.block.commonRightIdeal))

/-- The original left atom has the same two residual coordinates as
its tensor dictionary, plus one fixed row vector. -/
theorem ordinaryLeftPoint_eq_translation (hpacket : packet.Realizes)
    (h : Arithmetic.Orbit c) (i : AllocationColumn K packet.leaf.leftSlots)
    (hi : i ∈ packet.leftReindex.cartesian) :
    packet.ordinaryLeftPoint h i = packet.leftRowTranslation h +
      rawSourceLocation (CanonicalLiteralLocations.plain packet.firstSign)
        (CanonicalLiteralLocations.plain packet.firstSign)
        (CanonicalLiteralLocations.prime packet.firstSign) i := by
  have hresidual : (packet.block.leftResidual (packet.leftReindex.index i)).val =
      allocationColumnIdeal i := packet.leftReindex.ideal_product i hi
  have hnonzero : allocationColumnIdeal i ≠ 0 := by
    intro hz
    exact (packet.block.leftResidual (packet.leftReindex.index i)).property.1
      (hresidual.trans hz)
  have hleft : i.1.1 ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [allocationColumnIdeal, hz, zero_mul])
  have hright : i.1.2 ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [allocationColumnIdeal, hz, mul_zero, zero_mul])
  have hfirst : packet.second.physical.first.poolPower.val *
      (packet.second.physical.source.ideal (packet.leftReindex.index i)).val =
      (packet.second.physical.first.poolPower.val * packet.block.commonLeftIdeal.val) *
        allocationColumnIdeal i := by
    have hsource :
        (packet.second.physical.source.ideal (packet.leftReindex.index i)).val =
          packet.block.commonLeftIdeal.val *
            (packet.block.leftResidual (packet.leftReindex.index i)).val :=
      packet.block.left_reconstruct _ _ (packet.leftReindex_mem_common i hi)
    rw [hsource, hresidual]
    exact (mul_assoc _ _ _).symm
  have hsecond : (packet.block.secondLeftIdeal (packet.leftReindex.index i)).val =
      packet.block.commonLeftIdeal.val * allocationColumnIdeal i := by
    change packet.block.commonLeftIdeal.val *
      (packet.block.leftResidual (packet.leftReindex.index i)).val = _
    exact congrArg (fun J : Ideal (𝓞 K) => packet.block.commonLeftIdeal.val * J) hresidual
  have hx := CanonicalLiteralLocations.actual_product_locations packet.firstSign
    (Real.log (CanonicalSecondLogChart.rowRadius packet.second.stage.radius
      packet.key.2.1.val h).val) i hleft hright _ _
    (packet.second.physical.first.poolPower.val * packet.block.commonLeftIdeal.val)
    packet.block.commonLeftIdeal.val
    (mul_ne_zero packet.second.physical.first.poolPower.property.1
      packet.block.commonLeftIdeal.property.1)
    packet.block.commonLeftIdeal.property.1 hfirst hsecond
  change WithLp.toLp 2
    (packet.second.physical.firstPoint (packet.leftReindex.index i),
      packet.chart.leftPoint h (packet.leftReindex.index i)) = _
  rw [(packet.realizes_point hpacket) (packet.leftReindex.index i),
    (packet.realizes_second hpacket).leftPoint]
  simpa only [leftRowTranslation, firstSign, SArithmeticData.exteriorNorm,
    DedekindZetaZeroFree.idealNorm, RawLeafPacket.block, SourceClassKey.block,
    SecondSource.block, map_mul, Nat.cast_mul] using hx

/-- Conjugation reverses the first Fourier sign once on the right;
the second coordinate remains the same negative residual logarithm. -/
theorem ordinaryRightPoint_eq_translation (hpacket : packet.Realizes)
    (h : Arithmetic.Orbit c) (i : AllocationColumn K packet.leaf.rightSlots)
    (hi : i ∈ packet.rightReindex.cartesian) :
    packet.ordinaryRightPoint h i = packet.rightRowTranslation h +
      rawSourceLocation (CanonicalLiteralLocations.plain (-packet.firstSign))
        (CanonicalLiteralLocations.plain (-packet.firstSign))
        (CanonicalLiteralLocations.prime (-packet.firstSign)) i := by
  have hresidual : (packet.block.rightResidual (packet.rightReindex.index i)).val =
      allocationColumnIdeal i := packet.rightReindex.ideal_product i hi
  have hnonzero : allocationColumnIdeal i ≠ 0 := by
    intro hz
    exact (packet.block.rightResidual (packet.rightReindex.index i)).property.1
      (hresidual.trans hz)
  have hleft : i.1.1 ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [allocationColumnIdeal, hz, zero_mul])
  have hright : i.1.2 ≠ 0 := by
    intro hz
    exact hnonzero (by simp only [allocationColumnIdeal, hz, mul_zero, zero_mul])
  have hfirst : packet.second.physical.first.poolPower.val *
      (packet.second.physical.source.ideal (packet.rightReindex.index i)).val =
      (packet.second.physical.first.poolPower.val * packet.block.commonRightIdeal.val) *
        allocationColumnIdeal i := by
    have hsource :
        (packet.second.physical.source.ideal (packet.rightReindex.index i)).val =
          packet.block.commonRightIdeal.val *
            (packet.block.rightResidual (packet.rightReindex.index i)).val :=
      packet.block.right_reconstruct _ _ (packet.rightReindex_mem_common i hi)
    rw [hsource, hresidual]
    exact (mul_assoc _ _ _).symm
  have hsecond : (packet.block.secondRightIdeal (packet.rightReindex.index i)).val =
      packet.block.commonRightIdeal.val * allocationColumnIdeal i := by
    change packet.block.commonRightIdeal.val *
      (packet.block.rightResidual (packet.rightReindex.index i)).val = _
    exact congrArg (fun J : Ideal (𝓞 K) => packet.block.commonRightIdeal.val * J) hresidual
  have hx := CanonicalLiteralLocations.actual_product_locations (-packet.firstSign) 0
    i hleft hright _ _
    (packet.second.physical.first.poolPower.val * packet.block.commonRightIdeal.val)
    packet.block.commonRightIdeal.val
    (mul_ne_zero packet.second.physical.first.poolPower.property.1
      packet.block.commonRightIdeal.property.1)
    packet.block.commonRightIdeal.property.1 hfirst hsecond
  change WithLp.toLp 2
    (-packet.second.physical.firstPoint (packet.rightReindex.index i),
      packet.chart.rightPoint h (packet.rightReindex.index i)) = _
  rw [(packet.realizes_point hpacket) (packet.rightReindex.index i),
    (packet.realizes_second hpacket).rightPoint]
  simpa only [rightRowTranslation, firstSign, SArithmeticData.exteriorNorm,
    DedekindZetaZeroFree.idealNorm, RawLeafPacket.block, SourceClassKey.block,
    SecondSource.block, map_mul, Nat.cast_mul, neg_neg, neg_mul, zero_sub] using hx

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryLeftPoint_eq_translation
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryRightPoint_eq_translation
