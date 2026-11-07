module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8CommonScalarBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleCompensation

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual exceptional common scalars retain both frozen ideals

The N8 pointwise frozen-atom estimate applies to every original
occurrence branch.  At the second extraction the slot dictionary is
the actual first atom table, with its original two-tilt profile.
Membership in the full first atlas supplies the original profile
window without an ordinary-row predicate.
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

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

theorem t3b_firstCommonScalar_sq_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (side : Bool) :
    ‖packet.firstCommonScalar side‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) := by
  have h := packet.firstCommonScalar_sq_le input horders side
  rw [← packet.firstFrozenExterior_val side] at h
  exact h

theorem t3b_second_witness_original_slot (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) :
    (packet.secondBranch side).witness.2 i ∈
      call.workingRaw.exteriorSlots (packet.firstAtomIndex hpacket side i) :=
  packet.t3b_firstAtlas_slot_mem hpacket side i _
    (Finset.mem_filter.mp ((packet.secondBranch side).witness_slots i)).1

/-- The bound is for the literal first atom table on the whole carrier,
including rows later classified as exceptional. -/
def t3b_secondCommonAtomBounds (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.secondBranch side).CommonAtomBounds
      (phases.characters false (packet.firstAtomIndex hpacket side)) call.base
      (fun i => call.originalLength (packet.firstAtomIndex hpacket side i))
      (packet.firstAtomTable hpacket phases side).slotWeight where
  base_pos := call.base_pos
  annulus _ := 2 * call.prepared.upper
  profile _ := input.frozenAmplitude ^ 2
  annulus_nonneg _ := input.commonAnnulus_nonneg
  profile_nonneg _ := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (packet.firstAtomIndex hpacket side) _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (packet.firstAtomIndex hpacket side) _)
  prime _ _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _
    (phases.characters_mask_zero_or_one false (packet.firstAtomIndex hpacket side) _)
  prime_annulus i _ :=
    (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
      (input.original_slot_window (packet.firstAtomIndex hpacket side i) _
        (packet.t3b_second_witness_original_slot hpacket side i)).2
  slot i _ := by
    have hw := input.original_slot_window (packet.firstAtomIndex hpacket side i) _
      (packet.t3b_second_witness_original_slot hpacket side i)
    exact pow_le_pow_left₀ (norm_nonneg _)
      (input.tilted_prime_norm_le (p := p) horders
        (packet.firstAtomIndex hpacket side i) _ hw) 2

theorem t3b_secondCommonScalar_sq_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) (side : Bool) :
    ‖(packet.firstAtomTable hpacket phases side).commonScalar
        (packet.secondBranch side)‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) := by
  let I : (Arithmetic.data c).Exterior :=
    if side then primePowerProduct packet.R.primes packet.R.rightMultiplicity
    else primePowerProduct packet.R.primes packet.R.leftMultiplicity
  have hI : frozenSourceIdeal (packet.secondBranch side).plainDivisor₁
        (packet.secondBranch side).plainDivisor₂ (packet.secondBranch side).keep
        (packet.secondBranch side).witness.2 = I.val := by
    change N4.secondFrozenIdeal packet side = I.val
    rw [N4.secondFrozenIdeal_eq]
    cases side with
    | false => exact packet.block.common_left.symm
    | true => exact packet.block.common_right.symm
  have h := N8CommonScalar.bareCommonScalar_sq_le
    (packet.t3b_secondCommonAtomBounds hpacket input horders phases side)
    (Arithmetic.context c) I hI input.frozenAtomBudget c.geometry.slots
    input.frozenAtomBudget_one (packet.t3b_firstAtlas_slots_le hpacket side)
    (fun _ => le_max_right _ _)
  rw [← hI] at h
  exact h

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_firstCommonScalar_sq_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_secondCommonScalar_sq_le
