import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPlainCharts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinarySecondExceptionalBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual exceptional source records for both original rectangles

The centered source retains the complete subtraction and its four
quotient scales. The uncentered source uses its actual ordinary value.
Both source records are produced from the four single-ideal charts and
share exactly the same original allocation and raw normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet)

theorem t3bUnscaled_centered (side : Bool) :
    (packet.t3bUnscaledTable hpacket phases side).centered = call.node.centered := by
  cases side <;> rfl

theorem t3bComparisonWeight_centered (side : Bool) (hc : call.node.centered = true) :
    (packet.t3bUnscaledTable hpacket phases side).comparisonWeight true =
      (packet.t3bUnscaledTable hpacket phases side).leftWeight true := by
  simp only [OrdinaryAtomTable.comparisonWeight, packet.t3bUnscaled_centered, hc,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]

theorem t3bComparisonWeight_uncentered (side : Bool) (hc : call.node.centered = false) :
    (packet.t3bUnscaledTable hpacket phases side).comparisonWeight true = fun _ => 0 := by
  simp only [OrdinaryAtomTable.comparisonWeight, packet.t3bUnscaled_centered, hc,
    Bool.not_false, Bool.and_self, if_true]

def t3bScaleProduct (side : Bool) : ℝ :=
  packet.t3bQuotientScale hpacket phases side false false *
    packet.t3bQuotientScale hpacket phases side false true

theorem t3bQuotientScale_product (side rectangle : Bool) :
    packet.t3bQuotientScale hpacket phases side rectangle false *
        packet.t3bQuotientScale hpacket phases side rectangle true =
      packet.t3bScaleProduct hpacket phases side := by
  change (_ / _) * (_ / _) = (_ / _) * (_ / _)
  rw [div_mul_div_comm, div_mul_div_comm, packet.t3bUnscaled_scale_product]

def t3bScaleLower (side : Bool) : ℝ :=
  min (min (packet.t3bQuotientScale hpacket phases side false false)
      (packet.t3bQuotientScale hpacket phases side false true))
    (min (packet.t3bQuotientScale hpacket phases side true false)
      (packet.t3bQuotientScale hpacket phases side true true))

theorem t3bScaleLower_pos (side : Bool) :
    0 < packet.t3bScaleLower hpacket phases side :=
  lt_min (lt_min (packet.t3bQuotientScale_pos hpacket phases side false false)
    (packet.t3bQuotientScale_pos hpacket phases side false true))
    (lt_min (packet.t3bQuotientScale_pos hpacket phases side true false)
      (packet.t3bQuotientScale_pos hpacket phases side true true))

theorem t3bScaleLower_le (side rectangle plain : Bool) :
    packet.t3bScaleLower hpacket phases side ≤
      packet.t3bQuotientScale hpacket phases side rectangle plain := by
  cases rectangle <;> cases plain
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

def t3bExceptionalAt (input : ProfileInput call) (hc : call.node.centered = true)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bUnscaledSource hpacket phases side).ExceptionalAt (σ := Arithmetic.embedding c)
      ((packet.t3bUnscaledTable hpacket phases side).scale₁ true)
      ((packet.t3bUnscaledTable hpacket phases side).scale₂ true)
      (fun _ => (packet.t3bUnscaledTable hpacket phases side).comparisonWeight true)
      (fun _ => (packet.t3bUnscaledTable hpacket phases side).rightWeight true)
      (CanonicalExceptionalVolume.coefficient
        (call.localizedData.plainBackground * packet.t3bOriginalCharacter phases h))
      (packet.t3bPlainProfile hpacket phases input side false ξ)
      (packet.t3bPlainProfile hpacket phases input side true ξ) ξ h where
  mask := packet.t3bCompleteMask phases h
  time := T3b.time (packet.t3bFourierSign side) (t3bFourierMode side ξ)
  product := packet.t3bScaleProduct hpacket phases side
  lower := packet.t3bScaleLower hpacket phases side
  lower_pos := packet.t3bScaleLower_pos hpacket phases side
  X₁_lower := by
    cases side <;> exact packet.t3bScaleLower_le hpacket phases _ false false
  X₂_lower := by
    cases side <;> exact packet.t3bScaleLower_le hpacket phases _ false true
  Y₁_lower := packet.t3bScaleLower_le hpacket phases side true false
  Y₂_lower := packet.t3bScaleLower_le hpacket phases side true true
  productX := by
    cases side <;> exact packet.t3bQuotientScale_product hpacket phases _ false
  productY := packet.t3bQuotientScale_product hpacket phases side true
  chartX₁ := by
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ false false ξ h
  chartX₂ := by
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ false true ξ h
  chartY₁ := by
    simp only [packet.t3bComparisonWeight_centered hpacket phases side hc]
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ true false ξ h
  chartY₂ := by
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ true true ξ h

def t3bOrdinaryExceptionalAt (input : ProfileInput call)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bUnscaledSource hpacket phases side).OrdinaryExceptionalAt
      (σ := Arithmetic.embedding c)
      (CanonicalExceptionalVolume.coefficient
        (call.localizedData.plainBackground * packet.t3bOriginalCharacter phases h))
      (packet.t3bPlainProfile hpacket phases input side false ξ)
      (packet.t3bPlainProfile hpacket phases input side true ξ) ξ h where
  mask := packet.t3bCompleteMask phases h
  time := T3b.time (packet.t3bFourierSign side) (t3bFourierMode side ξ)
  product := packet.t3bScaleProduct hpacket phases side
  lower := packet.t3bScaleLower hpacket phases side
  lower_pos := packet.t3bScaleLower_pos hpacket phases side
  X₁_lower := by
    cases side <;> exact packet.t3bScaleLower_le hpacket phases _ false false
  X₂_lower := by
    cases side <;> exact packet.t3bScaleLower_le hpacket phases _ false true
  productX := by
    cases side <;> exact packet.t3bQuotientScale_product hpacket phases _ false
  chartX₁ := by
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ false false ξ h
  chartX₂ := by
    cases side <;> exact packet.t3bPlainChart hpacket phases input _ false true ξ h

theorem t3bUnscaledLeftFrame_normalizer :
    (packet.t3bUnscaledLeftFrame hpacket phases).normalizer = 1 := by
  change extraGaussNormalizer 1 1 (fun _ => 1) = 1
  simp only [extraGaussNormalizer, SecondCoefficientTermDictionary.centralNormalizer,
    Real.sqrt_one, Complex.ofReal_one, inv_one, Finset.prod_const_one, mul_one]

theorem t3bUnscaledRightFrame_normalizer :
    (packet.t3bUnscaledRightFrame hpacket phases).normalizer = 1 := by
  change extraGaussNormalizer 1 1 (fun _ => 1) = 1
  simp only [extraGaussNormalizer, SecondCoefficientTermDictionary.centralNormalizer,
    Real.sqrt_one, Complex.ofReal_one, inv_one, Finset.prod_const_one, mul_one]

theorem t3b_centeredColumn_uncentered (hc : call.node.centered = false)
    (side : Bool) (ξ : EngineParameter) (h : packet.R.live) :
    (packet.t3bUnscaledSource hpacket phases side).centeredColumn
        (σ := Arithmetic.embedding c)
        ((packet.t3bUnscaledTable hpacket phases side).scale₁ true)
        ((packet.t3bUnscaledTable hpacket phases side).scale₂ true)
        (fun _ => (packet.t3bUnscaledTable hpacket phases side).comparisonWeight true)
        (fun _ => (packet.t3bUnscaledTable hpacket phases side).rightWeight true) ξ h =
      (packet.t3bUnscaledSource hpacket phases side).ordinaryColumn
        (σ := Arithmetic.embedding c) ξ h := by
  rw [packet.t3bComparisonWeight_uncentered hpacket phases side hc]
  simp only [ActualAllocatedSource.centeredColumn, ActualAllocatedSource.ordinaryColumn,
    rawSourceCoefficient, FixedChildCharacters.coefficient, childCartesianCoefficient,
    sourcePlainTerm, mul_zero, zero_mul, sub_zero]

theorem t3b_left_centered_value (input : ProfileInput call) (hc : call.node.centered = true)
    (ξ : EngineParameter) (h : packet.R.live) :
    ‖jointFourierColumn (packet.t3bUnscaledLeftFrame hpacket phases).allocation.columns
      ((packet.t3bUnscaledLeftFrame hpacket phases).centeredCoefficient
        (packet.t3bUnscaledLeftComparison hpacket phases) h.val)
      (rawSourceLocation ((packet.t3bUnscaledLeftFrame hpacket phases).leftLocation h.val)
        ((packet.t3bUnscaledLeftFrame hpacket phases).rightLocation h.val)
        ((packet.t3bUnscaledLeftFrame hpacket phases).slotLocation h.val)) ξ‖ =
      ‖(packet.t3bExceptionalAt hpacket phases input hc false ξ h).source.value‖ := by
  rw [SecondSideFrame.centered_column_norm_eq_source,
    packet.t3bUnscaledLeftFrame_normalizer, norm_one, one_mul]
  rfl

theorem t3b_right_centered_value (input : ProfileInput call) (hc : call.node.centered = true)
    (ξ : EngineParameter) (h : packet.R.live) :
    ‖jointFourierColumn (packet.t3bUnscaledRightFrame hpacket phases).allocation.columns
      ((packet.t3bUnscaledRightFrame hpacket phases).centeredCoefficient
        (packet.t3bUnscaledRightComparison hpacket phases) h.val)
      (rawSourceLocation ((packet.t3bUnscaledRightFrame hpacket phases).leftLocation h.val)
        ((packet.t3bUnscaledRightFrame hpacket phases).rightLocation h.val)
        ((packet.t3bUnscaledRightFrame hpacket phases).slotLocation h.val)) ξ‖ =
      ‖(packet.t3bExceptionalAt hpacket phases input hc true ξ h).source.value‖ := by
  rw [SecondSideFrame.centered_column_norm_eq_source,
    packet.t3bUnscaledRightFrame_normalizer, norm_one, one_mul]
  rfl

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bExceptionalAt
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bOrdinaryExceptionalAt
