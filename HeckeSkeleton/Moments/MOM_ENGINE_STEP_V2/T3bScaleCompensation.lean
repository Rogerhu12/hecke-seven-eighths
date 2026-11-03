import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4FrozenIdeals

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two original exceptional scale products

Both extractions retain their literal prime occurrences and the same
quotient plain scales. Their lower annulus comes from the fixed profile
window, before any call or branch. The complete frozen ideals occur in
the compensation, including the full pool valuation at the first step.
No ordinary restriction or estimate for a completed child is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace T3b

/-- A single fixed annulus controls either direction of norm/scale. -/
def profileAnnulus (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (max (profileRange c frame).expanded.upper
    (profileRange c frame).expanded.lower⁻¹)

theorem profileAnnulus_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ profileAnnulus c frame := le_max_left _ _

theorem profileAnnulus_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < profileAnnulus c frame := zero_lt_one.trans_le (profileAnnulus_one_le c frame)

theorem profileWindow_lower (c : TargetContext K) (frame : SourceFrame) :
    profileWindow c frame ⊆ Set.Ici (profileAnnulus c frame)⁻¹ := by
  intro x hx
  have hle : (profileRange c frame).expanded.lower⁻¹ ≤ profileAnnulus c frame :=
    (le_max_right _ _).trans (le_max_right _ _)
  have h := one_div_le_one_div_of_le
    (inv_pos.mpr (profileRange c frame).expanded.lower_pos) hle
  simp only [one_div, inv_inv] at h
  exact h.trans hx.1

theorem profileWindow_upper (c : TargetContext K) (frame : SourceFrame) :
    profileWindow c frame ⊆ Set.Iic (profileAnnulus c frame) := by
  intro x hx
  exact hx.2.trans ((le_max_left _ _).trans (le_max_right _ _))

private theorem apply_of_heq {α : Type} {m n : ℕ} (hc : m = n)
    (f : Fin m → α) (g : Fin n → α) (he : HEq f g) (i : Fin m) :
    f i = g (Fin.cast hc i) := by
  subst n
  exact congrFun (eq_of_heq he) i

private theorem prod_fin_cast {m n : ℕ} (hc : m = n) (f : Fin n → ℝ) :
    (∏ i : Fin m, f (Fin.cast hc i)) = ∏ i : Fin n, f i := by
  subst n
  rfl

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace Call

variable (call)

theorem t3b_original_prime_scale_le (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ call.workingRaw.exteriorSlots i) :
    call.base ^ call.originalLength i ≤ T3b.profileAnnulus c call.frame *
      (Ideal.absNorm q.asIdeal : ℝ) := by
  exact input.localized.primeScale_le_annulus_mul_norm
    (T3b.profileAnnulus c call.frame) call.base 0
    (T3b.profileAnnulus_pos c call.frame) call.base_pos (Set.mem_univ _)
    ((call.t3b_window_subset input).trans (T3b.profileWindow_lower c call.frame))
    i q (Finset.mem_filter.mp hq).1

theorem t3b_original_prime_norm_le (input : ProfileInput call)
    (i : Fin call.localizedData.geometry.slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ call.workingRaw.exteriorSlots i) :
    (Ideal.absNorm q.asIdeal : ℝ) ≤ T3b.profileAnnulus c call.frame *
      call.base ^ call.originalLength i := by
  have hp := ((call.localizedData.geometry.slots i).support_spec 0
    (call.base ^ call.originalLength i) q).mp (Finset.mem_filter.mp hq).1
  have hr : input.localized.primeRep i 0
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i) ≠ 0 := by
    intro hzero
    exact hp ((input.localized.prime_eq i 0 _).trans hzero)
  have hw := call.t3b_window_subset input
    (input.localized.prime_support i 0 (Set.mem_univ _) hr)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
    (T3b.profileWindow_upper c call.frame hw)

end Call

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

/-- The full first retained carrier, not its ordinary subfamily. -/
theorem t3b_firstAtlas_slot_mem (side : Bool)
    (i : Fin (packet.firstAtlas side).slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ (packet.firstAtlas side).reindex.slots i) :
    q ∈ call.workingRaw.exteriorSlots (packet.firstAtomIndex hpacket side i) := by
  have he := T3b.apply_of_heq (packet.realizes_firstCount hpacket side).symm
    (packet.firstAtlas side).reindex.slots
    (fun j : Fin (packet.firstBranch side).keep.card =>
      SupportCartesian.primeLive
        (call.workingRaw.exteriorSlots (SlotRestriction.index (packet.firstBranch side).keep j))
        packet.second.physical.first.fullDeletion)
    (packet.realizes_firstSlots hpacket side) i
  rw [he] at hq
  exact (Finset.mem_filter.mp hq).1

include hpacket in
theorem t3b_firstAtlas_slots_le (side : Bool) :
    (packet.firstAtlas side).slotCount ≤ c.geometry.slots := by
  rw [← packet.realizes_firstCount hpacket side]
  have h : (packet.firstBranch side).keep.card ≤ call.localizedData.geometry.slotCount := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (packet.firstBranch side).keep
  exact h.trans call.slots_le

theorem t3b_firstScaleProduct_eq (side : Bool) :
    packet.firstScaleProduct side =
      (packet.firstBranch side).residualGaussScale call.base call.originalLength
        (call.originalPlainScale false false) (call.originalPlainScale false true) := rfl

theorem t3b_firstScaleProduct_full (side rectangle : Bool) :
    packet.firstPlainScale side rectangle false * packet.firstPlainScale side rectangle true *
        ∏ i : Fin (packet.firstAtlas side).slotCount,
          call.base ^ call.originalLength (packet.firstAtomIndex hpacket side i) =
      packet.firstScaleProduct side := by
  exact (congrArg
    (fun value : ℝ => packet.firstPlainScale side rectangle false *
      packet.firstPlainScale side rectangle true * value)
    (T3b.prod_fin_cast (packet.realizes_firstCount hpacket side).symm
      (fun i : Fin (packet.firstBranch side).keep.card =>
        call.base ^ call.originalLength
          (SlotRestriction.index (packet.firstBranch side).keep i)))).trans
    (packet.firstScaleProduct_rectangle side rectangle)

/-- The literal scale product immediately before the inner divisor. -/
def t3bBeforeScaleProduct (side : Bool) : ℝ :=
  (packet.secondBranch side).residualGaussScale call.base
    (fun i => call.originalLength (packet.firstAtomIndex hpacket side i))
    (packet.firstPlainScale side false false) (packet.firstPlainScale side false true)

theorem t3bBeforeScaleProduct_pos (side : Bool) :
    0 < packet.t3bBeforeScaleProduct hpacket side :=
  (packet.secondBranch side).residualGaussScale_pos _ _ _ _ call.base_pos
    (packet.firstPlainScale_pos side false false) (packet.firstPlainScale_pos side false true)

theorem t3bUnscaled_scale_total (phases : OriginalPhaseData packet) (side : Bool) :
    (packet.t3bUnscaledTable hpacket phases side).scale₁ false *
      (packet.t3bUnscaledTable hpacket phases side).scale₂ false *
      (∏ i, call.base ^ (packet.t3bUnscaledTable hpacket phases side).length i) =
        packet.t3bBeforeScaleProduct hpacket side := by
  cases side <;> rfl

theorem t3b_firstScale_compensated (input : ProfileInput call) (side : Bool) :
    call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) ≤
      (T3b.profileAnnulus c call.frame) ^ c.geometry.slots *
        (packet.firstScaleProduct side * (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ)) := by
  have h := (packet.firstBranch side).originalScale_le_compensated
    call.base call.originalLength
    (call.originalPlainScale false false) (call.originalPlainScale false true)
    (T3b.profileAnnulus c call.frame) c.geometry.slots call.base_pos
    (N4.originalPlainScale_pos false false).le (N4.originalPlainScale_pos false true).le
    (T3b.profileAnnulus_one_le c call.frame) call.slots_le
    (fun i _ => call.t3b_original_prime_scale_le input i
      ((packet.firstBranch side).witness.2 i)
      (Finset.mem_filter.mp ((packet.firstBranch side).witness_slots i)).1)
  rw [N4.originalScaleProduct_eq] at h
  exact h

theorem t3b_secondScale_compensated (input : ProfileInput call) (side : Bool) :
    packet.firstScaleProduct side ≤
      (T3b.profileAnnulus c call.frame) ^ c.geometry.slots *
        (packet.t3bBeforeScaleProduct hpacket side *
          (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ)) := by
  have h := (packet.secondBranch side).originalScale_le_compensated
    call.base (fun i => call.originalLength (packet.firstAtomIndex hpacket side i))
    (packet.firstPlainScale side false false) (packet.firstPlainScale side false true)
    (T3b.profileAnnulus c call.frame) c.geometry.slots call.base_pos
    (packet.firstPlainScale_pos side false false).le (packet.firstPlainScale_pos side false true).le
    (T3b.profileAnnulus_one_le c call.frame) (packet.t3b_firstAtlas_slots_le hpacket side)
    (fun i _ => call.t3b_original_prime_scale_le input
      (packet.firstAtomIndex hpacket side i) ((packet.secondBranch side).witness.2 i)
      (packet.t3b_firstAtlas_slot_mem hpacket side i _
        (Finset.mem_filter.mp ((packet.secondBranch side).witness_slots i)).1))
  rw [packet.t3b_firstScaleProduct_full hpacket side false] at h
  exact h

theorem t3b_firstScale_upper (input : ProfileInput call) (side : Bool) :
    packet.firstScaleProduct side * (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) ≤
      (T3b.profileAnnulus c call.frame) ^ c.geometry.slots *
        call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) := by
  have h := N4.residualGaussScale_mul_frozenNorm_le (packet.firstBranch side)
    call.base call.originalLength
    (call.originalPlainScale false false) (call.originalPlainScale false true)
    (T3b.profileAnnulus c call.frame) c.geometry.slots call.base_pos
    (N4.originalPlainScale_pos false false).le (N4.originalPlainScale_pos false true).le
    (T3b.profileAnnulus_one_le c call.frame) call.slots_le
    (fun i _ => call.t3b_original_prime_norm_le input i
      ((packet.firstBranch side).witness.2 i)
      (Finset.mem_filter.mp ((packet.firstBranch side).witness_slots i)).1)
  rw [N4.originalScaleProduct_eq] at h
  exact h

theorem t3b_secondScale_upper (input : ProfileInput call) (side : Bool) :
    packet.t3bBeforeScaleProduct hpacket side *
        (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) ≤
      (T3b.profileAnnulus c call.frame) ^ c.geometry.slots * packet.firstScaleProduct side := by
  have h := N4.residualGaussScale_mul_frozenNorm_le (packet.secondBranch side)
    call.base (fun i => call.originalLength (packet.firstAtomIndex hpacket side i))
    (packet.firstPlainScale side false false) (packet.firstPlainScale side false true)
    (T3b.profileAnnulus c call.frame) c.geometry.slots call.base_pos
    (packet.firstPlainScale_pos side false false).le (packet.firstPlainScale_pos side false true).le
    (T3b.profileAnnulus_one_le c call.frame) (packet.t3b_firstAtlas_slots_le hpacket side)
    (fun i _ => call.t3b_original_prime_norm_le input
      (packet.firstAtomIndex hpacket side i) ((packet.secondBranch side).witness.2 i)
      (packet.t3b_firstAtlas_slot_mem hpacket side i _
        (Finset.mem_filter.mp ((packet.secondBranch side).witness_slots i)).1))
  rw [packet.t3b_firstScaleProduct_full hpacket side false] at h
  exact h

include hpacket in
theorem t3b_poolNorm_le_firstFrozenNorm (side : Bool) :
    (Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ≤
      (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) := by
  rw [N4.firstFrozenIdeal_eq hpacket side, map_mul, Nat.cast_mul]
  have hsel : 1 ≤ (Ideal.absNorm packet.second.physical.first.selected.val : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (nonZeroDivisors.coe_ne_zero packet.second.physical.first.selected))
  change (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ) ≤ _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsel
    (Nat.cast_nonneg (Ideal.absNorm packet.second.physical.first.poolPower.val))

/-- Both complete extracted ideals are paid, with a fixed annulus
cost for each original occurrence at each of the two extractions. -/
theorem t3b_twoScale_compensated (input : ProfileInput call) (side : Bool) :
    call.base ^ (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z) ≤
      (T3b.profileAnnulus c call.frame) ^ (2 * c.geometry.slots) *
        (packet.t3bBeforeScaleProduct hpacket side *
          ((Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) *
            (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ))) := by
  have h₁ := packet.t3b_firstScale_compensated input side
  have h₂ := packet.t3b_secondScale_compensated hpacket input side
  apply h₁.trans
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (Ideal.absNorm (N4.firstFrozenIdeal packet side))))
    (pow_nonneg (T3b.profileAnnulus_pos c call.frame).le c.geometry.slots)
  convert h using 1 <;> simp only [two_mul, pow_add] <;> ring

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_firstScale_compensated
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_twoScale_compensated
