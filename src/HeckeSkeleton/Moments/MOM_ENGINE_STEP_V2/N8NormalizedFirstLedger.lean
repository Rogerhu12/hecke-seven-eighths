module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedScaleBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedSecondLedger
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4FrozenIdeals

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual first external scalars cancel the first scale loss

Both original occurrence covers extract the same selected first ideal
and the complete original pool valuation. Their central factors cancel
the two original negative scale powers. The remaining tilt costs at
most nine source losses, before the first Cauchy outer ledger is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace N8ScalarWindow

theorem sigma_le_one (c : TargetContext K) : recipeInductionSigma c ≤ 1 :=
  min_le_left _ _

end N8ScalarWindow

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem firstFrozenExterior_eq (hpacket : packet.Realizes) (side : Bool) :
    (packet.firstFrozenExterior side).val =
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val := by
  rw [← packet.firstFrozenExterior_val side]
  exact N4.firstFrozenIdeal_eq hpacket side

theorem poolPower_norm_nominal (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) :
    (Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower =
      call.base ^ (packet.nominal false).skeleton.w := by
  change (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ) =
    call.base ^ (packet.nominal false).tag.removedLength call.base
  rw [N4.nominal_tag_eq hpacket false]
  exact N4.poolPower_norm phases

theorem firstFrozenExterior_norm (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool) :
    (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ) =
      call.base ^ ((packet.nominal false).skeleton.c + (packet.nominal false).skeleton.w) := by
  have hc : (Ideal.absNorm packet.second.physical.first.selected.val : ℝ) =
      call.base ^ (packet.nominal false).skeleton.c := by
    change _ = call.base ^ idealLogLength call.base (packet.nominal false).ideals.first.val
    rw [N4.nominal_first_eq hpacket false]
    exact (rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero packet.second.physical.first.selected)).symm
  have hw : (Ideal.absNorm packet.second.physical.first.poolPower.val : ℝ) =
      call.base ^ (packet.nominal false).skeleton.w :=
    packet.poolPower_norm_nominal hpacket phases
  rw [packet.firstFrozenExterior_eq hpacket side, map_mul, Nat.cast_mul, hc, hw,
    ← Real.rpow_add call.base_pos]

theorem firstCentralExponent_nominal (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool) :
    packet.firstCentralExponent side =
      (packet.nominal false).skeleton.A - (packet.nominal false).skeleton.c -
        (packet.nominal false).skeleton.w := by
  change (packet.nominal false).skeleton.A -
      Real.log (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ) / Real.log call.base = _
  rw [packet.firstFrozenExterior_norm hpacket phases side, Real.log_rpow call.base_pos,
    mul_div_cancel_right₀ _ (Real.log_pos call.domain.scale).ne']
  ring

def firstScalarExponent : ℝ :=
  2 * ((packet.nominal false).skeleton.A - (packet.nominal false).skeleton.c -
      (packet.nominal false).skeleton.w) * (-1 + 2 * p.tilt) +
    2 * (packet.nominal false).skeleton.w * p.tilt -
      ((packet.nominal false).skeleton.c + (packet.nominal false).skeleton.w)

theorem firstExternalPair_le (input : ProfileInput call) (hpacket : packet.Realizes)
    (horders : (0, 0) ∈ input.orders) (phases : OriginalPhaseData packet) :
    packet.firstExternalPair ≤
      (input.frozenAtomBudget ^ c.geometry.slots *
        N8ScalarWindow.reciprocal c call.frame ^ (2 * c.geometry.slots)) *
          call.base ^ packet.firstScalarExponent := by
  let A := input.frozenAtomBudget ^ c.geometry.slots
  let R := N8ScalarWindow.reciprocal c call.frame
  let G := (packet.nominal false).skeleton
  let U := Real.sqrt (A / call.base ^ (G.c + G.w))
  let W := call.base ^ (G.w * p.tilt)
  let V := call.base ^ ((G.A - G.c - G.w) * (-1 + 2 * p.tilt))
  have hbase : 0 < call.base := call.base_pos
  have hA : 0 ≤ A := pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _
  have hR : 0 ≤ R := zero_le_one.trans (N8ScalarWindow.reciprocal_one c call.frame)
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hW : 0 ≤ W := Real.rpow_nonneg hbase.le _
  have hV : 0 ≤ V := Real.rpow_nonneg hbase.le _
  have hs (side : Bool) :
      ‖packet.firstExternalScalar side‖ ≤ U * W * (R ^ c.geometry.slots * V) := by
    have hscale := packet.firstScaleProduct_power_le input side
    rw [packet.firstCentralExponent_nominal hpacket phases side] at hscale
    have h := (packet.firstExternalScalar_norm_le input horders side).trans
      (mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.rpow_nonneg ((Arithmetic.data c).exteriorNorm_pos _).le _)))
    rw [packet.firstFrozenExterior_norm hpacket phases side,
      packet.poolPower_norm_nominal hpacket phases, ← Real.rpow_mul call.base_pos.le] at h
    exact h
  have hU2 : U * U = A / call.base ^ (G.c + G.w) :=
    Real.mul_self_sqrt (div_nonneg hA (Real.rpow_nonneg hbase.le _))
  have hpowers : (W * W) * (V * V) =
      call.base ^ (2 * G.w * p.tilt + 2 * (G.A - G.c - G.w) * (-1 + 2 * p.tilt)) := by
    dsimp only [W, V]
    rw [← Real.rpow_add hbase, ← Real.rpow_add hbase, ← Real.rpow_add hbase]
    congr 1
    ring
  calc
    packet.firstExternalPair ≤
        (U * W * (R ^ c.geometry.slots * V)) *
          (U * W * (R ^ c.geometry.slots * V)) :=
      mul_le_mul (hs false) (hs true) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hU hW) (mul_nonneg (pow_nonneg hR _) hV))
    _ = (U * U) * R ^ (2 * c.geometry.slots) * ((W * W) * (V * V)) := by
      rw [two_mul c.geometry.slots, pow_add]
      ring
    _ = (A * R ^ (2 * c.geometry.slots)) *
        (call.base ^ (2 * G.w * p.tilt + 2 * (G.A - G.c - G.w) * (-1 + 2 * p.tilt)) /
          call.base ^ (G.c + G.w)) := by
      rw [hU2, hpowers]
      ring
    _ = _ := by
      rw [← Real.rpow_sub hbase]
      congr 2
      dsimp only [firstScalarExponent, G]
      ring

/-- This is precisely the first allowance quotient, together with the
single original pool index allowance. -/
def firstOuterExponent : ℝ :=
  (packet.nominal false).skeleton.R + (packet.nominal false).skeleton.E -
    (packet.nominal false).skeleton.c + (packet.nominal false).boundary -
    call.workingParameters.m + (packet.nominal false).skeleton.wo +
    (packet.nominal false).tag.poolLength (recipeInductionSigma c)

theorem first_tilt_le :
    (2 * (packet.nominal false).skeleton.w +
      4 * ((packet.nominal false).skeleton.A - (packet.nominal false).skeleton.c -
        (packet.nominal false).skeleton.w)) * p.tilt ≤ 9 * p.loss := by
  have hc : 0 ≤ (packet.nominal false).skeleton.c :=
    idealLogLength_nonneg call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero (packet.nominal false).ideals.first)
  have hw : 0 ≤ (packet.nominal false).skeleton.w :=
    (packet.nominal false).tag.removedLength_nonneg call.base call.domain.scale
  have hA : (packet.nominal false).skeleton.A ≤ 9 / 4 := by
    have h := N8Source.working_total_le call
    have hs := N8ScalarWindow.sigma_le_one c
    change (packet.nominal false).skeleton.A ≤ N8Source.originalLengthBound c at h
    dsimp only [N8Source.originalLengthBound] at h
    linarith
  calc
    _ ≤ 9 * p.tilt := mul_le_mul_of_nonneg_right (by linarith) p.tilt_pos.le
    _ ≤ 9 * p.loss := mul_le_mul_of_nonneg_left p.tilt_le_loss (by norm_num)

theorem first_second_exponent_le :
    packet.firstScalarExponent + packet.secondLedgerExponent ≤
      packet.firstOuterExponent + 29 * p.loss + packet.annulusLog / 6 +
        call.node.parameters.κ * (momentMesh K c.family).val := by
  have he : packet.firstScalarExponent + packet.secondLedgerExponent =
      packet.firstOuterExponent + 20 * p.loss + packet.annulusLog / 6 +
        call.node.parameters.κ * (momentMesh K c.family).val +
          (2 * (packet.nominal false).skeleton.w +
            4 * ((packet.nominal false).skeleton.A - (packet.nominal false).skeleton.c -
              (packet.nominal false).skeleton.w)) * p.tilt := by
    unfold firstScalarExponent secondLedgerExponent firstOuterExponent
    rw [← N8Source.working_width call]
    have hq : (packet.nominal false).skeleton.q = call.workingParameters.q := rfl
    rw [hq]
    ring
  rw [he]
  linarith [packet.first_tilt_le]

/-- The original first scalar pair pays its entire central scale
loss; only the original first outer and one pool allowance remain. -/
theorem firstExternalPair_mul_secondLedger_le (input : ProfileInput call)
    (hpacket : packet.Realizes) (horders : (0, 0) ∈ input.orders)
    (phases : OriginalPhaseData packet) :
    packet.firstExternalPair * call.base ^ packet.secondLedgerExponent ≤
      (input.frozenAtomBudget ^ c.geometry.slots *
        N8ScalarWindow.reciprocal c call.frame ^ (2 * c.geometry.slots)) *
      call.base ^ (packet.firstOuterExponent + 29 * p.loss + packet.annulusLog / 6 +
        call.node.parameters.κ * (momentMesh K c.family).val) := by
  calc
    _ ≤ ((input.frozenAtomBudget ^ c.geometry.slots *
          N8ScalarWindow.reciprocal c call.frame ^ (2 * c.geometry.slots)) *
            call.base ^ packet.firstScalarExponent) * call.base ^ packet.secondLedgerExponent :=
      mul_le_mul_of_nonneg_right (packet.firstExternalPair_le input hpacket horders phases)
        (Real.rpow_nonneg call.base_pos.le _)
    _ = (input.frozenAtomBudget ^ c.geometry.slots *
        N8ScalarWindow.reciprocal c call.frame ^ (2 * c.geometry.slots)) *
        call.base ^ (packet.firstScalarExponent + packet.secondLedgerExponent) := by
      rw [mul_assoc, ← Real.rpow_add call.base_pos]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le packet.first_second_exponent_le)
      (mul_nonneg (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _)
        (pow_nonneg (zero_le_one.trans (N8ScalarWindow.reciprocal_one c call.frame)) _))

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstExternalPair_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstExternalPair_mul_secondLedger_le
