import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCommonBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCoverOrigin

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Both actual common scalars in the unchanged normalizer

The second support extraction uses the first atlas's original slot
dictionary.  Its tilted weights are the original profiles at the same
prime occurrences.  The two bounds are then multiplied in the exact
normalizer used for every passive label and comparison rectangle.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def secondFrozenExterior (side : Bool) : (Arithmetic.data c).Exterior :=
  extractedExterior
    (packet.second.physical.source.ideal
      ((packet.firstAtlas side).reindex.index (packet.secondBranch side).witness))
    (primeSupport packet.key.1.val.1)

theorem secondFrozenExterior_val (side : Bool) :
    frozenSourceIdeal (packet.secondBranch side).plainDivisor₁
      (packet.secondBranch side).plainDivisor₂ (packet.secondBranch side).keep
      (packet.secondBranch side).witness.2 = (packet.secondFrozenExterior side).val := by
  change _ = supportExtract
    (packet.second.physical.source.ideal
      ((packet.firstAtlas side).reindex.index (packet.secondBranch side).witness)).val
    (primeSupport packet.key.1.val.1)
  rw [(packet.firstAtlas side).reindex.ideal_product (packet.secondBranch side).witness
    ((packet.secondBranch side).original_subset (packet.secondBranch side).witness_mem)]
  exact (packet.secondBranch side).frozenSourceIdeal_eq.trans
    ((packet.secondBranch side).extract_ideal _ (packet.secondBranch side).witness_mem).symm

end RawLeafPacket

namespace OriginalOccurrenceData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (D : OriginalOccurrenceData O)

theorem second_witness_original_slot (hpacket : packet.Realizes) (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) :
    (packet.secondBranch side).witness.2 i ∈
      call.workingRaw.exteriorSlots (D.firstIndex side i) := by
  have h := (Finset.mem_filter.mp ((packet.secondBranch side).witness_slots i)).1
  rw [D.firstAtlas_slots hpacket side i] at h
  exact (Finset.mem_filter.mp h).1

include D in
theorem firstAtlas_count_le (side : Bool) :
    (packet.firstAtlas side).slotCount ≤ c.geometry.slots := by
  rw [← D.first_count side]
  have h : (packet.firstBranch side).keep.card ≤ call.localizedData.geometry.slotCount := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (packet.firstBranch side).keep)
  exact h.trans call.slots_le

def secondCommonAtomBounds (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.secondBranch side).CommonAtomBounds
      (phases.characters false (D.firstIndex side)) call.base
      (fun i => call.originalLength (D.firstIndex side i)) (D.firstSlotWeight side) where
  base_pos := call.base_pos
  annulus _ := 2 * call.prepared.upper
  profile _ := input.frozenAmplitude ^ 2
  annulus_nonneg _ := input.commonAnnulus_nonneg
  profile_nonneg _ := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (D.firstIndex side) _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (D.firstIndex side) _)
  prime _ _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (D.firstIndex side) _)
  prime_annulus i _ :=
    (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
      (input.original_slot_window (D.firstIndex side i) _
        (D.second_witness_original_slot hpacket side i)).2
  slot i _ := by
    have hw := input.original_slot_window (D.firstIndex side i) _
      (D.second_witness_original_slot hpacket side i)
    exact pow_le_pow_left₀ (norm_nonneg _)
      (input.tilted_prime_norm_le (p := p) horders (D.firstIndex side i) _ hw) 2

theorem secondCommonScalar_sq_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    ‖D.secondCommonScalar phases side‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.secondFrozenExterior side).val : ℝ) := by
  exact N8CommonScalar.bareCommonScalar_sq_le
    (D.secondCommonAtomBounds input hpacket horders phases side)
    (Arithmetic.context c) (packet.secondFrozenExterior side)
    (packet.secondFrozenExterior_val side) input.frozenAtomBudget c.geometry.slots
    input.frozenAtomBudget_one (D.firstAtlas_count_le side) (fun _ => le_max_right _ _)

theorem secondCommonScalar_norm_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    ‖D.secondCommonScalar phases side‖ ≤
      Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.secondFrozenExterior side).val : ℝ)) :=
  N8CommonScalar.norm_le_sqrt_of_sq_le _ _
    (D.secondCommonScalar_sq_le input hpacket horders phases side)

/-- Every factor is the one in the original normalizer; the expression
is independent of the later passive label and of the rectangle. -/
def normalizerBound (_D : OriginalOccurrenceData O) (input : ProfileInput call)
    (side : Bool) : ℝ :=
  (Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots /
      (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ)) *
    ((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ^ p.tilt) *
    (packet.firstScaleProduct side ^ (-1 + 2 * p.tilt))) *
      Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.secondFrozenExterior side).val : ℝ))

theorem normalizer_norm_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    ‖D.normalizer phases side‖ ≤ D.normalizerBound input side := by
  have hfirst := packet.firstExternalScalar_norm_le input horders side
  have hsecond := D.secondCommonScalar_norm_le input hpacket horders phases side
  change ‖packet.firstExternalScalar side * D.secondCommonScalar phases side‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hfirst hsecond (norm_nonneg _)
    ((norm_nonneg _).trans hfirst)

theorem normalizer_sq_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    ‖D.normalizer phases side‖ ^ 2 ≤ D.normalizerBound input side ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _)
    (D.normalizer_norm_le input hpacket horders phases side) 2

theorem normalizer_pair_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) :
    ‖D.normalizer phases false‖ * ‖D.normalizer phases true‖ ≤
      D.normalizerBound input false * D.normalizerBound input true := by
  have hleft := D.normalizer_norm_le input hpacket horders phases false
  exact mul_le_mul hleft (D.normalizer_norm_le input hpacket horders phases true)
    (norm_nonneg _) ((norm_nonneg _).trans hleft)

end OriginalOccurrenceData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.secondCommonScalar_sq_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.normalizer_pair_le
