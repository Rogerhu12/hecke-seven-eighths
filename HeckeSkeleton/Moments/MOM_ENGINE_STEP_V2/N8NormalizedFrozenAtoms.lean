import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCanonical
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedPassiveMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8CommonScalarBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual passive scalar retains its own divisor denominator

The carrier, characters and profile formula are the canonical N2 data.
The only analytic input is the original point-evaluation seminorm.  A
frozen prime belongs to that same original smooth support, so its norm
and the two-tilt power are bounded on the original annulus.  The finite
allocation theorem then keeps the inverse norm of its actual divisor.
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

namespace OrdinarySeed

variable {packet : RawLeafPacket call p} (seed : OrdinarySeed packet)
variable (input : ProfileInput call) (support : seed.ordinary.PassiveSupport input)

theorem n8_primeProfile_zero (side : Bool) (i : Fin (seed.ordinary.residualSlotCount side))
    (x : ℝ) (hx : 0 < x) :
    (seed.primeProfile input side i).formula.value 0 x =
      (call.node.data.geometry.slots (seed.slotIndex side i)).profile 0 x *
        ((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) := by
  simp [primeProfile, profile, ProfileFormula.value, ProfileFormula.linear,
    ParentProfileKind.representative, OriginalOccurrenceData.normPower, hx,
    input.raw.prime_eq]

theorem passive_witness_slot
    (hsupport : seed.CanonicalSupport input support) (side : Bool)
    (a : support.labels side) (i : Fin (seed.ordinary.residualSlotCount side)) :
    ((PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a).witness.2 i) ∈
      (call.node.data.geometry.slots (seed.slotIndex side i)).support 0
        (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) := by
  let B := PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a
  have hm := B.witness_mem
  simp only [pairedAllocatedColumns, childCartesianColumns, Finset.product_eq_sprod,
    Finset.mem_product] at hm
  have hp := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hm.2 i)).1
  change B.witness.2 i ∈ (support.side side).slotCarrier
    packet.second.physical.first.paidSupport i at hp
  have hs := (Finset.mem_filter.mp hp).1
  simpa [SmoothSideSupport.smoothSlot, SmoothSideSupport.length, hsupport.prime side i,
    hsupport.slots side, primeProfile, profile] using hs

theorem passive_witness_window
    (hsupport : seed.CanonicalSupport input support) (side : Bool)
    (a : support.labels side) (i : Fin (seed.ordinary.residualSlotCount side)) :
    ((Ideal.absNorm
        ((PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a).witness.2 i).asIdeal : ℝ) /
      call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) ∈ call.window := by
  have hslot := seed.passive_witness_slot input support hsupport side a i
  have hprofile := ((call.node.data.geometry.slots (seed.slotIndex side i)).support_spec
    0 (call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) _).mp hslot
  have hrep : input.raw.primeRep (seed.slotIndex side i) 0
      ((Ideal.absNorm
        ((PassiveAllocation.allocation (support.carrier side) seed.ordinary.passiveMask a).witness.2 i).asIdeal : ℝ) /
        call.base ^ (call.node.data.geometry.slots (seed.slotIndex side i)).length) ≠ 0 := by
    intro hzero
    exact hprofile ((input.raw.prime_eq (seed.slotIndex side i) 0 _).trans hzero)
  exact input.raw.prime_support (seed.slotIndex side i) 0 (Set.mem_univ _) hrep

include input support in
theorem residualSlotCount_le (side : Bool) :
    seed.ordinary.residualSlotCount side ≤ c.geometry.slots := by
  have hc := Fintype.card_le_of_injective (support.side side).slotEmbedding
    (support.side side).slotEmbedding_injective
  have hc' : seed.ordinary.residualSlotCount side ≤ call.node.data.geometry.slotCount := by
    simpa only [Fintype.card_fin] using hc
  exact hc'.trans call.slots_le

/-- Each actual passive frozen scalar keeps the norm of that same
passive divisor. Neither a duplicate label nor a larger source cost is
chosen to obtain the estimate. -/
theorem canonicalSource_frozenScalar_bound
    (hsupport : seed.CanonicalSupport input support) (horders : (0, 0) ∈ input.orders)
    (side : Bool) (a : support.labels side) (rectangle : Bool)
    (h : seed.ordinary.rows.live)
    (hh : h ∈ (seed.canonicalSource input support side a rectangle).rows) :
    ‖(seed.canonicalSource input support side a rectangle).frozenScalar
        (σ := Arithmetic.embedding c) h‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots / (Ideal.absNorm a.val.1 : ℝ) := by
  let s := seed.canonicalSource input support side a rectangle
  have hannulus : 0 ≤ 2 * call.prepared.upper := by
    have hu := call.prepared.lower_pos.trans_le call.prepared.interval
    positivity
  apply s.frozenScalar_uniform_inverse_norm (Arithmetic.context c)
    (fun _ => 2 * call.prepared.upper) (fun _ => input.frozenAmplitude ^ 2)
    input.frozenAtomBudget c.geometry.slots input.frozenAtomBudget_one
    (seed.residualSlotCount_le input support side)
    (fun _ => hannulus) (fun _ => sq_nonneg _)
    (fun _ => le_max_right _ _)
    (PassiveAllocation.label_divisor_squarefree (support.carrier side) seed.ordinary.passiveMask a)
    (PassiveAllocation.label_selection (support.carrier side) seed.ordinary.passiveMask a)
    ?_ ?_ ?_ ?_ ?_ h hh
  · intro r hr
    exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one true (seed.slotIndex side) _)
  · intro r hr
    exact OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one true (seed.slotIndex side) _)
  · intro r hr i hi
    exact OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _
      (seed.phases.characters_mask_zero_or_one true (seed.slotIndex side) _)
  · intro i hi
    have hw := seed.passive_witness_window input support hsupport side a i
    exact (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp hw.2
  · intro r hr i hi
    have hw := seed.passive_witness_window input support hsupport side a i
    have hb := input.tilted_prime_norm_le (p := p) horders (seed.slotIndex side i) _ hw
    rw [← seed.n8_primeProfile_zero input side i _ (call.window_positive hw)] at hb
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem canonicalSource_scalarCost_bound
    (hsupport : seed.CanonicalSupport input support) (horders : (0, 0) ∈ input.orders)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    SourceCost.scalar (seed.canonicalSource input support side a rectangle) ≤
      input.frozenAtomBudget ^ c.geometry.slots / (Ideal.absNorm a.val.1 : ℝ) := by
  apply SourceCost.scalar_le
  · exact div_nonneg (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _)
      (Nat.cast_nonneg _)
  · exact seed.canonicalSource_frozenScalar_bound input support hsupport horders
      side a rectangle

theorem canonicalSource_scalarCost_uniform
    (hsupport : seed.CanonicalSupport input support) (horders : (0, 0) ∈ input.orders)
    (side : Bool) (a : support.labels side) (rectangle : Bool) :
    SourceCost.scalar (seed.canonicalSource input support side a rectangle) ≤
      input.frozenAtomBudget ^ c.geometry.slots := by
  have hnorm : (1 : ℝ) ≤ Ideal.absNorm a.val.1 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (PassiveAllocation.label_divisor_ne_zero (support.carrier side)
          seed.ordinary.passiveMask a))
  apply (seed.canonicalSource_scalarCost_bound input support hsupport horders
    side a rectangle).trans
  exact div_le_self (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _) hnorm

end OrdinarySeed
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.passive_witness_slot
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_frozenScalar_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_scalarCost_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.canonicalSource_scalarCost_uniform
