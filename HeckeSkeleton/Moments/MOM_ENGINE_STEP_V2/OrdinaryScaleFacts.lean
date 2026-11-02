import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOccurrenceFacts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryNormPower

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Both original comparison rectangles have the same scale product

In the centered case the two comparison exponents add to the original
plain length. In the ordinary case the actual working source uses the
same plain scales for its unused comparison. The two genuine support
extractions divide both rectangles by identical original divisors.
The common norm-power scalar is therefore independent of the rectangle.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

variable (call : Call c)

theorem originalPlainScale_product (rectangle : Bool) :
    call.originalPlainScale rectangle false * call.originalPlainScale rectangle true =
      call.originalPlainScale false false * call.originalPlainScale false true := by
  cases rectangle with
  | false => rfl
  | true =>
    cases h : call.node.centered with
    | false =>
      simp only [originalPlainScale, workingComparison₁, workingComparison₂, h,
        Bool.false_eq_true, if_false, if_true]
    | true =>
      simp only [originalPlainScale, workingComparison₁, workingComparison₂, h,
        Bool.false_eq_true, if_false, if_true]
      rw [call.domain.comparison_left h, call.domain.comparison_right h,
        ← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos]
      congr 1
      ring

end Call

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem firstPlainScale_pos (side rectangle plain : Bool) :
    0 < packet.firstPlainScale side rectangle plain := by
  apply div_pos
  · unfold Call.originalPlainScale
    split_ifs <;> exact Real.rpow_pos_of_pos call.base_pos _
  · exact idealNorm_pos K _

theorem firstPlainScale_product (side rectangle : Bool) :
    packet.firstPlainScale side rectangle false * packet.firstPlainScale side rectangle true =
      packet.firstPlainScale side false false * packet.firstPlainScale side false true := by
  simp only [firstPlainScale, Bool.false_eq_true, if_false, if_true]
  rw [div_mul_div_comm, div_mul_div_comm, call.originalPlainScale_product rectangle]

theorem firstScaleProduct_pos (side : Bool) : 0 < packet.firstScaleProduct side := by
  apply mul_pos
  · exact mul_pos (packet.firstPlainScale_pos side false false)
      (packet.firstPlainScale_pos side false true)
  · exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos call.base_pos _)

theorem firstScaleProduct_rectangle (side rectangle : Bool) :
    packet.firstPlainScale side rectangle false * packet.firstPlainScale side rectangle true *
        ∏ i : Fin (packet.firstBranch side).keep.card,
          call.base ^ call.originalLength (SlotRestriction.index (packet.firstBranch side).keep i) =
      packet.firstScaleProduct side := by
  rw [packet.firstPlainScale_product side rectangle]
  rfl

end RawLeafPacket

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

theorem beforePlainScale_product (side rectangle : Bool) :
    D.beforePlainScale side rectangle false * D.beforePlainScale side rectangle true =
      D.beforePlainScale side false false * D.beforePlainScale side false true := by
  simp only [beforePlainScale, Bool.false_eq_true, if_false, if_true]
  rw [div_mul_div_comm, div_mul_div_comm, packet.firstPlainScale_product side rectangle]

theorem plainScale_product (side rectangle : Bool) :
    D.plainScale side rectangle false * D.plainScale side rectangle true =
      D.plainScale side false false * D.plainScale side false true := by
  simp only [plainScale, Bool.false_eq_true, if_false, if_true]
  rw [div_mul_div_comm, div_mul_div_comm, D.beforePlainScale_product side rectangle]

end OriginalOccurrenceData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Call.originalPlainScale_product
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstScaleProduct_rectangle
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.plainScale_product
