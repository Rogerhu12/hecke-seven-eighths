import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedFrozenAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSecondCarrier

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The independent inner divisor is retained in the actual row cost

The inner allocation precedes the passive mask refinement. Its witness
belongs to the twice restricted original prime support. Its frozen
scalar therefore has the same original annular profile estimate as the
passive scalar, while retaining its own, independent divisor denominator.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum WholeAllocation

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

namespace OrdinaryData

variable (O : OrdinaryData packet)

theorem originalAllocation_divisor (side : Bool) :
    (O.originalAllocation side).divisor = packet.allocation.1.val := by
  have h := congrArg (fun b => b.1.val) O.branch_eq
  cases side <;> exact h

theorem originalAllocation_squarefree (side : Bool) :
    Squarefree (O.originalAllocation side).divisor := by
  have h := (Finset.mem_filter.mp O.branch.property).2.1
  cases side <;> exact h

theorem originalAllocation_selection (side : Bool) :
    (O.originalAllocation side).selection ∈
      AllocationMass.idealAllocations (O.originalAllocation side).divisor
        (O.originalSlotCount side + 2) := by
  cases side
  · exact O.branch.val.2.2.1.property
  · exact O.branch.val.2.2.2.property

theorem originalAllocation_divisor_ne_zero (side : Bool) :
    (O.originalAllocation side).divisor ≠ 0 := by
  have h := (O.originalAllocation side).divisor_dvd_frozenIdeal
    (O.originalAllocation_squarefree side) (O.originalAllocation_selection side)
  intro hz
  rw [hz, zero_dvd_iff] at h
  exact (O.originalAllocation side).frozenIdeal_ne_zero h

theorem innerDivisor_ne_zero : packet.allocation.1.val ≠ 0 := by
  rw [← O.originalAllocation_divisor false]
  exact O.originalAllocation_divisor_ne_zero false

end OrdinaryData

namespace OriginalOccurrenceData

variable {O : OrdinaryData packet} (D : OriginalOccurrenceData O)

theorem originalSlotCount_le (side : Bool) :
    O.originalSlotCount side ≤ c.geometry.slots := by
  have hc := Fintype.card_le_of_injective (D.secondIndex side)
    (D.secondIndex_injective side)
  have hc' : O.originalSlotCount side ≤ call.node.data.geometry.slotCount := by
    simpa only [Fintype.card_fin] using hc
  exact hc'.trans call.slots_le

theorem inner_witness_slot (hpacket : packet.Realizes) (side : Bool)
    (i : Fin (O.originalSlotCount side)) :
    (O.originalAllocation side).witness.2 i ∈
      (call.node.data.geometry.slots (D.secondIndex side i)).support 0
        (call.base ^ (call.node.data.geometry.slots (D.secondIndex side i)).length) := by
  have hm := (O.originalAllocation side).witness_mem
  simp only [pairedAllocatedColumns, childCartesianColumns, Finset.product_eq_sprod,
    Finset.mem_product] at hm
  have hp := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hm.2 i)).1
  change (O.originalAllocation side).witness.2 i ∈
    (O.originalAllocation side).slots i at hp
  rw [D.originalAllocation_slots hpacket side i] at hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1

theorem inner_witness_window (input : ProfileInput call)
    (hpacket : packet.Realizes) (side : Bool) (i : Fin (O.originalSlotCount side)) :
    ((Ideal.absNorm ((O.originalAllocation side).witness.2 i).asIdeal : ℝ) /
      call.base ^ (call.node.data.geometry.slots (D.secondIndex side i)).length) ∈
        call.window := by
  have hslot := D.inner_witness_slot hpacket side i
  have hp := ((call.node.data.geometry.slots (D.secondIndex side i)).support_spec 0
    (call.base ^ (call.node.data.geometry.slots (D.secondIndex side i)).length) _).mp hslot
  have hrep : input.raw.primeRep (D.secondIndex side i) 0
      ((Ideal.absNorm ((O.originalAllocation side).witness.2 i).asIdeal : ℝ) /
        call.base ^ (call.node.data.geometry.slots (D.secondIndex side i)).length) ≠ 0 := by
    simpa only [input.raw.prime_eq] using hp
  exact input.raw.prime_support (D.secondIndex side i) 0 (Set.mem_univ _) hrep

end OriginalOccurrenceData

namespace OrdinarySeed

variable (seed : OrdinarySeed packet) (input : ProfileInput call)

theorem innerScalar_bound (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (side : Bool) (h : seed.ordinary.rows.live) :
    ‖seed.innerScalar side h‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm packet.allocation.1.val : ℝ) := by
  let O := seed.ordinary
  let B := O.originalAllocation side
  have hannulus : 0 ≤ 2 * call.prepared.upper := by
    have hu := call.prepared.lower_pos.trans_le call.prepared.interval
    positivity
  have hdiv : 0 < (Ideal.absNorm B.divisor : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (O.originalAllocation_divisor_ne_zero side)))
  have hscalar := B.scalar_norm_sq_le_divisor (Arithmetic.context c)
    (seed.phases.characters false (seed.occurrences.secondIndex side))
    ((O.originalSource side false).extractedFactor h)
    ((O.originalSource side false).row h).element call.base call.base_pos
    (seed.occurrences.beforeLength side) (seed.occurrences.beforeSlotWeight side)
    (fun _ => 2 * call.prepared.upper) (fun _ => input.frozenAmplitude ^ 2)
    (OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one false (seed.occurrences.secondIndex side) _))
    (OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one false (seed.occurrences.secondIndex side) _))
    (fun i _ => OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one false (seed.occurrences.secondIndex side) _))
    (fun i _ => (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
      (seed.occurrences.inner_witness_window input hpacket side i).2)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
      (input.tilted_prime_norm_le horders (seed.occurrences.secondIndex side i) _
        (seed.occurrences.inner_witness_window input hpacket side i)) 2)
    (fun _ => hannulus) (fun _ => sq_nonneg _)
    (O.originalAllocation_squarefree side) (O.originalAllocation_selection side)
  have hprod :
      (∏ i ∈ Finset.univ \ B.keep,
        (2 * call.prepared.upper) * input.frozenAmplitude ^ 2) ≤
          input.frozenAtomBudget ^ c.geometry.slots := by
    apply selected_factor_product_le _ _ _ _ input.frozenAtomBudget_one
      (by simpa only [Fintype.card_fin] using seed.occurrences.originalSlotCount_le side)
    · intro i hi
      exact mul_nonneg hannulus (sq_nonneg _)
    · intro i hi
      exact le_max_right _ _
  have hbound := hscalar.trans (div_le_div_of_nonneg_right hprod hdiv.le)
  simpa only [innerScalar, O.originalAllocation_divisor side] using hbound

theorem canonicalSource_rowCost_inner_bound (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (support : seed.ordinary.PassiveSupport input)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    {rowCost : ℝ} (hrowCost : 0 ≤ rowCost)
    (hrow : ∀ h ∈ (seed.ordinary.originalSource side false).rows,
      ‖(seed.ordinary.originalSource side false).weight h‖ ≤ rowCost) :
    SourceCost.row (seed.canonicalSource input support side a rectangle) ≤
      rowCost * (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm packet.allocation.1.val : ℝ)) := by
  apply seed.canonicalSource_rowCost_le support side a rectangle hrowCost
    (div_nonneg (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _)
      (Nat.cast_nonneg _)) hrow
  intro h hh
  exact seed.innerScalar_bound input hpacket horders side h

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryData.originalAllocation_divisor
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalOccurrenceData.inner_witness_slot
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.innerScalar_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_rowCost_inner_bound
