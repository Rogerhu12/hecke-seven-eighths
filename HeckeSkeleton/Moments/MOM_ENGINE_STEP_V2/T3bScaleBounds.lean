import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSources
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOriginalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4FrozenIdeals
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleArithmetic

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual centered plain scales and the independent inner divisor

The four plain scales retain the two original occurrence extractions
and the stored inner allocation. A plain divisor divides the complete
frozen ideal of its own extraction, including every removed slot.
The inner squarefree divisor also divides that same complete frozen
ideal because every prime selects a nonempty set of occurrences.

Consequently each side has its own exact norm loss. Selecting the
smaller second common ideal bounds the preceding loss by `c + w + b₂`
without spending any part of the independent inner-divisor saving.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

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

def t3bInnerFrozenIdeal (side : Bool) : Ideal (𝓞 K) :=
  (packet.t3bUnscaledSource hpacket phases side).allocation.frozenIdeal

theorem t3bInnerFrozenIdeal_ne_zero (side : Bool) :
    packet.t3bInnerFrozenIdeal hpacket phases side ≠ 0 :=
  (packet.t3bUnscaledSource hpacket phases side).allocation.frozenIdeal_ne_zero

def t3bInnerLoss (side : Bool) : ℝ :=
  idealLogLength call.base (packet.t3bInnerFrozenIdeal hpacket phases side)

theorem t3bInnerLoss_nonneg (side : Bool) :
    0 ≤ packet.t3bInnerLoss hpacket phases side :=
  idealLogLength_nonneg call.base call.domain.scale _
    (packet.t3bInnerFrozenIdeal_ne_zero hpacket phases side)

theorem t3b_innerDivisor_squarefree : Squarefree packet.allocation.1.val :=
  (Finset.mem_filter.mp packet.ordinaryAllocation.property).2.1

theorem t3b_innerDivisor_dvd_frozenIdeal (side : Bool) :
    packet.allocation.1.val ∣ packet.t3bInnerFrozenIdeal hpacket phases side := by
  cases side with
  | false =>
    exact (packet.t3bUnscaledSource hpacket phases false).allocation.divisor_dvd_frozenIdeal
      packet.t3b_innerDivisor_squarefree packet.allocation.2.2.1.property
  | true =>
    exact (packet.t3bUnscaledSource hpacket phases true).allocation.divisor_dvd_frozenIdeal
      packet.t3b_innerDivisor_squarefree packet.allocation.2.2.2.property

theorem t3b_innerDivisor_ne_zero : packet.allocation.1.val ≠ 0 := by
  have hmem := packet.allocation.1.property
  simp only [HeckePort.Moments.MobiusRegroup.divisorPool] at hmem
  obtain ⟨x, hx, hdiv⟩ := Finset.mem_biUnion.mp hmem
  exact LargeSieve.ne_bot_of_mem_idealDivisors hdiv

/-- Both sides pay the same actual independent inner divisor. -/
theorem t3b_innerDivisor_length_le (side : Bool) :
    idealLogLength call.base packet.allocation.1.val ≤
      packet.t3bInnerLoss hpacket phases side :=
  T3b.idealLogLength_mono call.base call.domain.scale _ _ packet.t3b_innerDivisor_ne_zero
    (packet.t3bInnerFrozenIdeal_ne_zero hpacket phases side)
    (packet.t3b_innerDivisor_dvd_frozenIdeal hpacket phases side)

theorem t3b_divisor_slotError_zero (side : Bool) :
    idealLogLength call.base packet.allocation.1.val -
      packet.t3bInnerLoss hpacket phases side ≤ 0 :=
  sub_nonpos.mpr (packet.t3b_innerDivisor_length_le hpacket phases side)

def t3bScaleLoss (side : Bool) : ℝ :=
  idealLogLength call.base (N4.firstFrozenIdeal packet side) +
    idealLogLength call.base (N4.secondFrozenIdeal packet side)

theorem t3bScaleLoss_nonneg (side : Bool) : 0 ≤ packet.t3bScaleLoss side :=
  add_nonneg
    (idealLogLength_nonneg call.base call.domain.scale _ (N4.firstFrozenIdeal_ne_zero packet side))
    (idealLogLength_nonneg call.base call.domain.scale _ (N4.secondFrozenIdeal_ne_zero packet side))

theorem t3bPlainScale_eq (side rectangle plain : Bool) :
    packet.t3bPlainScale hpacket phases side rectangle plain =
      packet.firstPlainScale side rectangle plain /
        idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
          else (packet.secondBranch side).plainDivisor₁) := by
  cases side <;> cases plain <;> rfl

theorem t3bQuotientScale_eq (side rectangle plain : Bool) :
    packet.t3bQuotientScale hpacket phases side rectangle plain =
      call.originalPlainScale rectangle plain /
        (idealNorm K (if plain then (packet.firstBranch side).plainDivisor₂
            else (packet.firstBranch side).plainDivisor₁) *
          idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
            else (packet.secondBranch side).plainDivisor₁) *
          idealNorm K (packet.t3bPlainDivisor hpacket phases side plain)) := by
  rw [t3bQuotientScale, packet.t3bPlainScale_eq hpacket phases, firstPlainScale]
  ring

theorem t3b_firstPlainDivisor_norm_le (side plain : Bool) :
    idealNorm K (if plain then (packet.firstBranch side).plainDivisor₂
        else (packet.firstBranch side).plainDivisor₁) ≤
      (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) :=
  norm_le_of_dvd (N4.firstFrozenIdeal_ne_zero packet side)
    (T3b.plainDivisor_dvd_frozenSourceIdeal _ _ _ _ plain)

theorem t3b_secondPlainDivisor_norm_le (side plain : Bool) :
    idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
        else (packet.secondBranch side).plainDivisor₁) ≤
      (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) :=
  norm_le_of_dvd (N4.secondFrozenIdeal_ne_zero packet side)
    (T3b.plainDivisor_dvd_frozenSourceIdeal _ _ _ _ plain)

theorem t3b_innerPlainDivisor_norm_le (side plain : Bool) :
    idealNorm K (packet.t3bPlainDivisor hpacket phases side plain) ≤
      (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases side) : ℝ) :=
  norm_le_of_dvd (packet.t3bInnerFrozenIdeal_ne_zero hpacket phases side)
    (T3b.allocated_plainDivisor_dvd_frozenIdeal _ plain)

/-- Every original centered rectangle has the same lower exponent,
before a minimum over its four genuine quotient scales is taken. -/
theorem t3bQuotientScale_centered_lower (hc : call.node.centered = true)
    (side rectangle plain : Bool) :
    call.base ^ ((call.node.parameters.m + call.node.parameters.q) / 4 -
        packet.t3bScaleLoss side - packet.t3bInnerLoss hpacket phases side) ≤
      packet.t3bQuotientScale hpacket phases side rectangle plain := by
  have hfirst := packet.t3b_firstPlainDivisor_norm_le side plain
  have hsecond := packet.t3b_secondPlainDivisor_norm_le side plain
  have hinner := packet.t3b_innerPlainDivisor_norm_le hpacket phases side plain
  have hden :
      idealNorm K (if plain then (packet.firstBranch side).plainDivisor₂
          else (packet.firstBranch side).plainDivisor₁) *
        idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
          else (packet.secondBranch side).plainDivisor₁) *
        idealNorm K (packet.t3bPlainDivisor hpacket phases side plain) ≤
      (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) *
        (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) *
        (Ideal.absNorm (packet.t3bInnerFrozenIdeal hpacket phases side) : ℝ) :=
    mul_le_mul (mul_le_mul hfirst hsecond (idealNorm_pos K _).le (Nat.cast_nonneg _))
      hinner (idealNorm_pos K _).le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [packet.t3bQuotientScale_eq hpacket phases]
  rw [Real.rpow_sub call.base_pos, Real.rpow_sub call.base_pos,
    t3bScaleLoss, Real.rpow_add call.base_pos,
    rpow_idealLogLength call.base call.domain.scale _ (N4.firstFrozenIdeal_ne_zero packet side),
    rpow_idealLogLength call.base call.domain.scale _ (N4.secondFrozenIdeal_ne_zero packet side),
    t3bInnerLoss, rpow_idealLogLength call.base call.domain.scale _
      (packet.t3bInnerFrozenIdeal_ne_zero hpacket phases side), div_div]
  have hsmall : 0 <
      idealNorm K (if plain then (packet.firstBranch side).plainDivisor₂
          else (packet.firstBranch side).plainDivisor₁) *
        idealNorm K (if plain then (packet.secondBranch side).plainDivisor₂
          else (packet.secondBranch side).plainDivisor₁) *
        idealNorm K (packet.t3bPlainDivisor hpacket phases side plain) :=
    mul_pos (mul_pos (idealNorm_pos K _) (idealNorm_pos K _)) (idealNorm_pos K _)
  apply (div_le_div_iff₀ (hsmall.trans_le hden) hsmall).mpr
  exact mul_le_mul (call.t3b_originalPlainScale_centered_lower hc rectangle plain) hden
    hsmall.le (N4.originalPlainScale_pos rectangle plain).le

theorem t3bScaleLower_centered_lower (hc : call.node.centered = true) (side : Bool) :
    call.base ^ ((call.node.parameters.m + call.node.parameters.q) / 4 -
        packet.t3bScaleLoss side - packet.t3bInnerLoss hpacket phases side) ≤
      packet.t3bScaleLower hpacket phases side :=
  le_min
    (le_min (packet.t3bQuotientScale_centered_lower hpacket phases hc side false false)
      (packet.t3bQuotientScale_centered_lower hpacket phases hc side false true))
    (le_min (packet.t3bQuotientScale_centered_lower hpacket phases hc side true false)
      (packet.t3bQuotientScale_centered_lower hpacket phases hc side true true))

include hpacket in
theorem t3b_nominal_first (side : Bool) :
    (packet.nominal side).ideals.first.val = packet.second.physical.first.selected.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).first side

include hpacket in
theorem t3b_nominal_second (side : Bool) :
    (packet.nominal side).ideals.second.val = packet.secondIdeal side := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).second side

include hpacket in
theorem t3b_nominal_secondOpposite (side : Bool) :
    (packet.nominal side).ideals.secondOpposite.val = packet.secondIdeal (!side) := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  cases side <;>
    exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).secondOpposite _

include hpacket in
theorem t3b_nominal_tag (side : Bool) :
    (packet.nominal side).tag = packet.second.physical.first.tag := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).tag side

include phases in
theorem t3b_poolLength_eq :
    idealLogLength call.base packet.second.physical.first.poolPower.val =
      packet.second.physical.first.tag.removedLength call.base := by
  have htag := phases.pool_tag
  have hpower := phases.pool_power
  cases hp : phases.pool with
  | none =>
    simp only [hp] at htag hpower
    rw [hpower]
    rcases htag with htag | htag <;>
      simp only [htag, OriginalNominalTag.removedLength, unitExterior, ← Ideal.one_eq_top,
        idealLogLength, map_one, Nat.cast_one, Real.log_one, zero_div]
  | some eq =>
    rcases eq with ⟨e, q⟩
    simp only [hp] at htag hpower
    rw [hpower, htag]
    exact idealLogLength_pow call.base q.val.asIdeal e.multiplicity

include hpacket phases in
theorem t3bScaleLoss_eq_nominal (side : Bool) :
    packet.t3bScaleLoss side =
      (packet.nominal side).skeleton.c + (packet.nominal side).skeleton.w +
        (packet.nominal side).skeleton.c₂ := by
  rw [t3bScaleLoss, N4.firstFrozenIdeal_eq hpacket side,
    T3b.idealLogLength_mul call.base _ _
      (nonZeroDivisors.coe_ne_zero packet.second.physical.first.selected)
      packet.second.physical.first.poolPower.property.1,
    packet.t3b_poolLength_eq phases, N4.secondFrozenIdeal_eq]
  change _ = idealLogLength call.base (packet.nominal side).ideals.first.val +
    (packet.nominal side).tag.removedLength call.base +
    idealLogLength call.base (packet.nominal side).ideals.second.val
  rw [packet.t3b_nominal_first hpacket, packet.t3b_nominal_tag hpacket,
    packet.t3b_nominal_second hpacket]

include hpacket in
theorem t3b_halfSecond_eq (side : Bool) :
    (packet.nominal side).halfSecond =
      (idealLogLength call.base (packet.secondIdeal side) +
        idealLogLength call.base (packet.secondIdeal (!side))) / 2 := by
  rw [OriginalNominalGeometry.halfSecond, packet.t3b_nominal_second hpacket,
    packet.t3b_nominal_secondOpposite hpacket]

/-- The side is selected from the original pair of second common
ideals. Both complete centered profiles remain attached to that side. -/
include hpacket phases in
theorem t3b_exists_small_second_side :
    ∃ side : Bool, packet.t3bScaleLoss side ≤
      (packet.nominal side).skeleton.c + (packet.nominal side).skeleton.w +
        (packet.nominal side).halfSecond := by
  by_cases h : idealLogLength call.base (packet.secondIdeal false) ≤
      idealLogLength call.base (packet.secondIdeal true)
  · refine ⟨false, ?_⟩
    rw [packet.t3bScaleLoss_eq_nominal hpacket phases, packet.t3b_halfSecond_eq hpacket]
    change _ + _ + idealLogLength call.base (packet.nominal false).ideals.second.val ≤ _
    rw [packet.t3b_nominal_second hpacket]
    change _ + _ + idealLogLength call.base (packet.secondIdeal false) ≤
      _ + _ + (idealLogLength call.base (packet.secondIdeal false) +
        idealLogLength call.base (packet.secondIdeal true)) / 2
    linarith
  · refine ⟨true, ?_⟩
    rw [packet.t3bScaleLoss_eq_nominal hpacket phases, packet.t3b_halfSecond_eq hpacket]
    change _ + _ + idealLogLength call.base (packet.nominal true).ideals.second.val ≤ _
    rw [packet.t3b_nominal_second hpacket]
    change _ + _ + idealLogLength call.base (packet.secondIdeal true) ≤
      _ + _ + (idealLogLength call.base (packet.secondIdeal true) +
        idealLogLength call.base (packet.secondIdeal false)) / 2
    linarith

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_innerDivisor_length_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bScaleLower_centered_lower
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exists_small_second_side
