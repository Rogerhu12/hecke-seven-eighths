import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryAtomExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryScaleFacts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original atom table before constructing an ordinary frame

The coordinates here are computed from the raw packet and its original
count proof. They do not require an already constructed ordinary frame.
After the frame is constructed these are definitionally the public
`OriginalOccurrenceData` coordinates.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

private theorem scaled_unitGaussExtract_term {k : ℕ}
    (d : OrdinaryAtomTable (K := K) k)
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
    {deletion : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch S₁ S₂ S deletion)
    (z : ℂ) (hn : d.normalizer = 1) (r : Bool)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    z * d.term r (b.reconstruct i) =
      ((d.unitGaussExtract b).scale (z * d.commonScalar b)).term r i := by
  rw [OrdinaryAtomTable.scale_term,
    OrdinaryAtomTable.unitGaussExtract_term d b r i hi, hn, one_mul]
  exact (mul_assoc _ _ _).symm

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

def ordinarySlots : Bool → ℕ
  | false => packet.leaf.leftSlots
  | true => packet.leaf.rightSlots

def firstAtomIndex (side : Bool) (i : Fin (packet.firstAtlas side).slotCount) :
    Fin call.localizedData.geometry.slotCount :=
  SlotRestriction.index (packet.firstBranch side).keep
    (Fin.cast (packet.realizes_firstCount hpacket side).symm i)

theorem secondAtomCount (side : Bool) :
    (packet.secondBranch side).keep.card = packet.ordinarySlots side := by
  cases side <;> rfl

def secondAtomIndex (side : Bool) (i : Fin (packet.ordinarySlots side)) :
    Fin call.localizedData.geometry.slotCount :=
  packet.firstAtomIndex hpacket side
    (SlotRestriction.index (packet.secondBranch side).keep
      (Fin.cast (packet.secondAtomCount side).symm i))

def normProfile (_packet : RawLeafPacket call p) (plain : Bool) (x : ℝ) : ℂ :=
  (if plain then call.localizedNormProfiles.right PUnit.unit 0 x
   else call.localizedNormProfiles.left PUnit.unit 0 x) *
    ((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ)

/-- The first residual table already includes the actual first,
pool and empty-divisor characters. Its common scalar is still outside. -/
def firstAtomTable (phases : OriginalPhaseData packet) (side : Bool) :
    OrdinaryAtomTable (K := K) (packet.firstAtlas side).slotCount where
  characters := phases.characters false (packet.firstAtomIndex hpacket side)
  centered := call.node.centered
  scale₁ r := packet.firstPlainScale side r false
  scale₂ r := packet.firstPlainScale side r true
  scale₁_pos r := packet.firstPlainScale_pos side r false
  scale₂_pos r := packet.firstPlainScale_pos side r true
  base := call.base
  base_gt_one := call.domain.scale
  length j := call.originalLength (packet.firstAtomIndex hpacket side j)
  length_pos j := (call.localizedData.geometry.slots (packet.firstAtomIndex hpacket side j)).length_pos
  leftWeight r I := packet.normProfile false (idealNorm K I / packet.firstPlainScale side r false)
  rightWeight r I := packet.normProfile true (idealNorm K I / packet.firstPlainScale side r true)
  slotWeight j q :=
    let original := packet.firstAtomIndex hpacket side j
    let x := (Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength original
    call.originalSlotWeight original q * ((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ)
  gauss₁ := 1
  gauss₂ := 1
  gaussSlot _ := 1
  gauss₁_pos := zero_lt_one
  gauss₂_pos := zero_lt_one
  gaussSlot_pos _ := zero_lt_one

@[simp] theorem firstAtomTable_normalizer (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.firstAtomTable hpacket phases side).normalizer = 1 := by
  simp [firstAtomTable, OrdinaryAtomTable.normalizer, extraGaussNormalizer,
    SecondCoefficientTermDictionary.centralNormalizer]

def secondAtomScalar (phases : OriginalPhaseData packet) (side : Bool) : ℂ :=
  packet.firstExternalScalar side *
    (packet.firstAtomTable hpacket phases side).commonScalar (packet.secondBranch side)

/-- This is the original second extraction. The prescribed complex
common scalar occurs in the first plain weight of both rectangles. -/
def beforeAtomTable (phases : OriginalPhaseData packet) :
    (side : Bool) → OrdinaryAtomTable (K := K) (packet.ordinarySlots side)
  | false =>
    ((packet.firstAtomTable hpacket phases false).unitGaussExtract
      (packet.secondBranch false)).scale (packet.secondAtomScalar hpacket phases false)
  | true =>
    ((packet.firstAtomTable hpacket phases true).unitGaussExtract
      (packet.secondBranch true)).scale (packet.secondAtomScalar hpacket phases true)

theorem beforeAtomTable_term (phases : OriginalPhaseData packet) (side : Bool)
    (r : Bool) (i : AllocationColumn K (packet.secondBranch side).keep.card)
    (hi : i ∈ (packet.secondBranch side).residualColumns) :
    packet.firstExternalScalar side *
        (packet.firstAtomTable hpacket phases side).term r
          ((packet.secondBranch side).reconstruct i) =
      (packet.beforeAtomTable hpacket phases side).term r
        (cast (congrArg (AllocationColumn K) (packet.secondAtomCount side)) i) := by
  have h := scaled_unitGaussExtract_term
    (packet.firstAtomTable hpacket phases side) (packet.secondBranch side)
    (packet.firstExternalScalar side)
    (packet.firstAtomTable_normalizer hpacket phases side) r i hi
  cases side <;> exact h

theorem ordinaryOccurrences_firstIndex (O : OrdinaryData packet) (side : Bool) :
    (packet.ordinaryOccurrences hpacket O).firstIndex side = packet.firstAtomIndex hpacket side := rfl

theorem ordinaryOccurrences_secondIndex (O : OrdinaryData packet) (side : Bool) :
    (packet.ordinaryOccurrences hpacket O).secondIndex side = packet.secondAtomIndex hpacket side := rfl

theorem ordinaryOccurrences_normalizer (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.ordinaryOccurrences hpacket O).normalizer phases side =
      packet.secondAtomScalar hpacket phases side := rfl

theorem original_norm_quotient
    (B I : HeckeGeneral.Analysis.NonzeroIdeal K) (N : ℝ) (hN : 0 < N) :
    idealNorm K (B * I) / N = idealNorm K I / (N / idealNorm K B) := by
  have hm : idealNorm K (B * I) = idealNorm K B * idealNorm K I := by
    change (Ideal.absNorm (B.val * I.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  rw [hm]
  field_simp [hN.ne', (idealNorm_pos K B).ne']

theorem beforeAtomTable_characters (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.beforeAtomTable hpacket phases side).characters =
      (packet.ordinaryOccurrences hpacket O).originalCharacters phases side := by
  cases side <;> rfl

theorem beforeAtomTable_base (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.beforeAtomTable hpacket phases side).base = call.base := by
  cases side <;> rfl

theorem beforeAtomTable_scale₁ (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side r : Bool) :
    (packet.beforeAtomTable hpacket phases side).scale₁ r =
      (packet.ordinaryOccurrences hpacket O).beforePlainScale side r false := by
  cases side <;> rfl

theorem beforeAtomTable_scale₂ (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side r : Bool) :
    (packet.beforeAtomTable hpacket phases side).scale₂ r =
      (packet.ordinaryOccurrences hpacket O).beforePlainScale side r true := by
  cases side <;> rfl

theorem beforeAtomTable_length (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side : Bool) (i : Fin (packet.ordinarySlots side)) :
    (packet.beforeAtomTable hpacket phases side).length i =
      (packet.ordinaryOccurrences hpacket O).beforeLength side i := by
  cases side <;> rfl

theorem beforeAtomTable_slotWeight (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side : Bool)
    (i : Fin (packet.ordinarySlots side)) (q : HeightOneSpectrum (𝓞 K)) :
    (packet.beforeAtomTable hpacket phases side).slotWeight i q =
      (packet.ordinaryOccurrences hpacket O).beforeSlotWeight side i q := by
  cases side <;> rfl

theorem beforeAtomTable_comparisonWeight (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.beforeAtomTable hpacket phases side).comparisonWeight r I =
      (packet.ordinaryOccurrences hpacket O).normalizer phases side *
        (packet.ordinaryOccurrences hpacket O).beforePlainWeight side r false I := by
  let d := packet.firstAtomTable hpacket phases side
  let b := packet.secondBranch side
  let z := packet.secondAtomScalar hpacket phases side
  have hscaled :
      (packet.beforeAtomTable hpacket phases side).comparisonWeight r I =
        z * d.comparisonWeight r (b.plainDivisor₁ * I) := by
    have h := ((d.unitGaussExtract b).scale_comparisonWeight z r I).trans
      (congrArg (fun value : ℂ => z * value)
        (d.unitGaussExtract_comparisonWeight b r I))
    cases side <;> exact h
  have hprofile : d.comparisonWeight r (b.plainDivisor₁ * I) =
      (packet.ordinaryOccurrences hpacket O).beforePlainWeight side r false I := by
    have hn := original_norm_quotient b.plainDivisor₁ I
      (packet.firstPlainScale side r false) (packet.firstPlainScale_pos side r false)
    simpa only [d, b, OrdinaryAtomTable.comparisonWeight, firstAtomTable,
      OriginalOccurrenceData.beforePlainWeight, OriginalOccurrenceData.beforePlainScale,
      OriginalOccurrenceData.plainProfile, OriginalOccurrenceData.normPower, normProfile,
      Bool.not_false, Bool.and_true, Bool.false_eq_true, if_false, ite_apply]
      using congrArg (fun x : ℝ =>
        if r && !call.node.centered then (0 : ℂ) else packet.normProfile false x) hn
  exact hscaled.trans ((congrArg (fun value : ℂ => z * value) hprofile).trans
    (congrArg (fun value : ℂ => value *
      (packet.ordinaryOccurrences hpacket O).beforePlainWeight side r false I)
      (packet.ordinaryOccurrences_normalizer hpacket O phases side).symm))

theorem beforeAtomTable_rightWeight (O : OrdinaryData packet)
    (phases : OriginalPhaseData packet) (side r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.beforeAtomTable hpacket phases side).rightWeight r I =
      (packet.ordinaryOccurrences hpacket O).beforePlainWeight side r true I := by
  cases side <;>
    change packet.normProfile true (idealNorm K (_ * I) / packet.firstPlainScale _ r true) =
      (if r && !call.node.centered && !true then 0 else packet.normProfile true
        (idealNorm K I / (packet.firstPlainScale _ r true / idealNorm K _))) <;>
    rw [original_norm_quotient _ I _ (packet.firstPlainScale_pos _ r true)] <;>
    simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true,
      Bool.true_eq_true, if_false, if_true]

theorem beforeAtomTable_normalizer (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.beforeAtomTable hpacket phases side).normalizer = 1 := by
  cases side with
  | false =>
      exact OrdinaryAtomTable.unitGaussExtract_normalizer
        (packet.firstAtomTable hpacket phases false) (packet.secondBranch false)
  | true =>
      exact OrdinaryAtomTable.unitGaussExtract_normalizer
        (packet.firstAtomTable hpacket phases true) (packet.secondBranch true)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.beforeAtomTable_term
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.ordinaryOccurrences_normalizer
