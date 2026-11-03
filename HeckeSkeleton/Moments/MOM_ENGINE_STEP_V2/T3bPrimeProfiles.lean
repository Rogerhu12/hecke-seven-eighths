import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSources
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleCompensation

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option Elab.async false

/-!
# The actual exceptional prime atoms use the original fixed profile window

The two retained occurrence maps are composed literally. Thus every
inner-allocation slot is an original prime occurrence, with its same
norm tilt and its same original Schwartz representative. The annulus
and finite evaluation orders are fixed before any call or row.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

variable (call : Call c)

theorem t3bPrimeProfile_support (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) :
    tsupport (input.localized.primeRep i 0) ⊆ T3b.profileWindow c call.frame :=
  (closure_minimal (input.localized.prime_support i 0 (Set.mem_univ _)) isClosed_Icc).trans
    (call.t3b_window_subset input)

def t3bPrimeNormProfile (p : SourceParameters c) (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) : 𝓢(ℝ, ℂ) :=
  CanonicalLogProfiles.shapeSchwartz (T3b.profileWindow c call.frame)
    (T3b.profileWindow_compact c call.frame) (T3b.profileWindow_positive c call.frame)
    (-1 + 2 * p.tilt) 0 (input.localized.primeRep i 0) (call.t3bPrimeProfile_support input i)

theorem t3bPrimeNormProfile_apply (p : SourceParameters c) (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) (x : ℝ) :
    call.t3bPrimeNormProfile p input i x =
      (call.localizedData.geometry.slots i).profile 0 x * ((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) := by
  rw [t3bPrimeNormProfile, CanonicalLogProfiles.shapeSchwartz_apply]
  change input.localized.primeRep i 0 x *
    (((x ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) * Complex.exp (Complex.I * (0 : ℂ) * (Real.log x : ℂ))) = _
  rw [input.localized.prime_eq]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]

end Call

namespace T3b

def primeOrders : Finset (ℕ × ℕ) := CanonicalLogProfiles.sourceOrders {(0, 0)}

theorem exists_primeProfile_bound (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (call : Call c) (input : ProfileInput call),
      call.frame = frame → primeOrders ⊆ input.orders →
      ∀ (i : Fin call.localizedData.geometry.slotCount) (x : ℝ),
        ‖call.t3bPrimeNormProfile p input i x‖ ≤ C * input.amplitude := by
  obtain ⟨C, hC, hb⟩ := CanonicalLogProfiles.shapeSchwartz_finset_bound
    (profileWindow c frame) (profileWindow_compact c frame) (profileWindow_positive c frame)
    (-1 + 2 * p.tilt) {(0, 0)}
  refine ⟨C, hC, ?_⟩
  intro call input hframe horders i x
  have hs : tsupport (input.localized.primeRep i 0) ⊆ profileWindow c frame := by
    simpa only [hframe] using call.t3bPrimeProfile_support input i
  have hshape := hb 0 (input.localized.primeRep i 0) hs
  simp only [abs_zero, add_zero, one_pow, mul_one] at hshape
  have hraw : primeOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (input.localized.primeRep i 0) ≤ input.amplitude := by
    apply (Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun q hq => Seminorm.le_finset_sup_apply (horders hq))).trans
    exact input.localized.prime_bound i 0 (Set.mem_univ _)
  have hbound := hshape.trans (mul_le_mul_of_nonneg_left hraw hC)
  have heval := SchwartzMap.norm_le_seminorm ℂ (call.t3bPrimeNormProfile p input i) x
  apply heval.trans
  simpa only [Call.t3bPrimeNormProfile, hframe, Finset.sup_singleton,
    SchwartzMap.schwartzSeminormFamily_apply] using hbound

end T3b

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)
variable (phases : OriginalPhaseData packet)

theorem t3bUnscaled_length (side : Bool) (i : Fin (packet.ordinarySlots side)) :
    (packet.t3bUnscaledTable hpacket phases side).length i =
      call.originalLength (packet.secondAtomIndex hpacket side i) := by
  cases side <;> rfl

private theorem firstAtomTable_primeNormProfile (input : ProfileInput call)
    (side : Bool) (i : Fin (packet.firstAtlas side).slotCount)
    (q : HeightOneSpectrum (𝓞 K)) :
    (packet.firstAtomTable hpacket phases side).slotWeight i q =
      call.t3bPrimeNormProfile p input (packet.firstAtomIndex hpacket side i)
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ call.originalLength (packet.firstAtomIndex hpacket side i)) := by
  exact (call.t3bPrimeNormProfile_apply p input (packet.firstAtomIndex hpacket side i)
    ((Ideal.absNorm q.asIdeal : ℝ) /
      call.base ^ call.originalLength (packet.firstAtomIndex hpacket side i))).symm

theorem t3bUnscaled_slotWeight (input : ProfileInput call)
    (side : Bool) (i : Fin (packet.ordinarySlots side)) (q : HeightOneSpectrum (𝓞 K)) :
    (packet.t3bUnscaledTable hpacket phases side).slotWeight i q =
      call.t3bPrimeNormProfile p input (packet.secondAtomIndex hpacket side i)
        ((Ideal.absNorm q.asIdeal : ℝ) /
          call.base ^ call.originalLength (packet.secondAtomIndex hpacket side i)) := by
  have h := packet.firstAtomTable_primeNormProfile hpacket phases input side
    (SlotRestriction.index (packet.secondBranch side).keep
      (Fin.cast (packet.secondAtomCount side).symm i)) q
  cases side <;> exact h

open HeckePort.Moments.Support in
private theorem residual_slot_mem
    {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (J : ι → A.Exterior)
    (hJ : ∀ j ∈ columns, (J j).val = supportResidual (ideal j).val P)
    (d : T.labels P D) (i : Fin (T.branch P D d).keep.card)
    (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (T.residualReindex P D J hJ d).slots i) :
    q ∈ T.reindex.slots (SlotRestriction.index (T.branch P D d).keep i) := by
  have he := congrFun
    (OrdinaryOriginalCoordinates.residualReindex_slots T P D J hJ d) i
  have hm : q ∈ SupportCartesian.primeLive
      (T.reindex.slots (SlotRestriction.index (T.branch P D d).keep i)) P :=
    (congrArg (fun S : Finset (HeightOneSpectrum (𝓞 K)) => q ∈ S) he).mp hq
  exact (Finset.mem_filter.mp hm).1

theorem t3bBefore_slot_mem (side : Bool) (i : Fin (packet.ordinarySlots side))
    (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (packet.t3bUnscaledSource hpacket phases side).allocation.slots i) :
    q ∈ call.workingRaw.exteriorSlots (packet.secondAtomIndex hpacket side i) := by
  cases side with
  | false =>
    have hm := residual_slot_mem (packet.firstAtlas false)
      (primeSupport packet.key.1.val.1) (packet.secondIdeal false)
      packet.block.leftResidual (fun j _ => packet.block.left_residual j)
      (packet.secondSupportKey false)
      (Fin.cast (packet.secondAtomCount false).symm i) q hq
    exact packet.t3b_firstAtlas_slot_mem hpacket false
      (SlotRestriction.index (packet.secondBranch false).keep
        (Fin.cast (packet.secondAtomCount false).symm i)) q hm
  | true =>
    have hm := residual_slot_mem (packet.firstAtlas true)
      (primeSupport packet.key.1.val.1) (packet.secondIdeal true)
      packet.block.rightResidual (fun j _ => packet.block.right_residual j)
      (packet.secondSupportKey true)
      (Fin.cast (packet.secondAtomCount true).symm i) q hq
    exact packet.t3b_firstAtlas_slot_mem hpacket true
      (SlotRestriction.index (packet.secondBranch true).keep
        (Fin.cast (packet.secondAtomCount true).symm i)) q hm

include hpacket in
theorem t3bUnscaled_slots_le (side : Bool) : packet.ordinarySlots side ≤ c.geometry.slots := by
  have h : (packet.secondBranch side).keep.card ≤ (packet.firstAtlas side).slotCount := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (packet.secondBranch side).keep
  exact (le_of_eq (packet.secondAtomCount side).symm).trans
    (h.trans (packet.t3b_firstAtlas_slots_le hpacket side))

theorem t3bUnscaled_mask_two (side : Bool) (I : Ideal (𝓞 K)) :
    (packet.t3bUnscaledTable hpacket phases side).characters.mask I = 0 ∨
      (packet.t3bUnscaledTable hpacket phases side).characters.mask I = 1 := by
  cases side
  all_goals
    change (if IsCoprime I (phases.mask false).val then (1 : ℂ) else 0) = 0 ∨
      (if IsCoprime I (phases.mask false).val then (1 : ℂ) else 0) = 1
    split_ifs <;> simp

theorem t3bUnscaled_prime_norm (input : ProfileInput call)
    (side : Bool) (i : Fin (packet.ordinarySlots side)) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (packet.t3bUnscaledSource hpacket phases side).allocation.slots i) :
    (Ideal.absNorm q.asIdeal : ℝ) ≤ T3b.profileAnnulus c call.frame *
      call.base ^ (packet.t3bUnscaledTable hpacket phases side).length i := by
  have hb := call.t3b_original_prime_norm_le input (packet.secondAtomIndex hpacket side i) q
    (packet.t3bBefore_slot_mem hpacket phases side i q hq)
  have he := congrArg
    (fun length : ℝ => T3b.profileAnnulus c call.frame * call.base ^ length)
    (packet.t3bUnscaled_length hpacket phases side i)
  exact hb.trans_eq he.symm

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3b.exists_primeProfile_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bUnscaled_prime_norm
