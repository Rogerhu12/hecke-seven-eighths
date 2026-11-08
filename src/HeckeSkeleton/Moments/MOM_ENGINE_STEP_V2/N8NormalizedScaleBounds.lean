module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedCommonBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceNormBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4ScaleProduct
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ClippedAnnulusSchedule

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed lower annulus and the original negative scale power

The same finite support schedule supplies a lower endpoint before any
call.  Every frozen occurrence is in that original support.  Its lower
norm window compensates the actual first extracted ideal, so the
negative two-tilt power is bounded without changing the normalizer.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
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

namespace N8ScalarWindow

def lower (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  let n := 6 * (widthBand (recipeInductionSigma c) 2 + 1)
  frame.lower / clippedAnnulusStep frame.upper n ^ n / 2

theorem lower_pos (c : TargetContext K) (frame : SourceFrame) :
    0 < lower c frame :=
  div_pos (div_pos frame.lower_pos (pow_pos (clippedAnnulusStep_pos _ _) _))
    (by norm_num)

def reciprocal (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (lower c frame)⁻¹

theorem reciprocal_one (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ reciprocal c frame := le_max_left _ _

theorem lower_le_call (input : ProfileInput call) :
    lower c call.frame ≤ call.prepared.lower / 2 := by
  rw [input.regular.lower]
  change call.frame.lower / clippedAnnulusStep call.frame.upper call.rankBound ^
      call.rankBound / 2 ≤
    (call.frame.lower / clippedAnnulusStep call.frame.upper call.rankBound ^
      (call.rankBound - call.rank)) / 2
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_left call.frame.lower_pos.le
      (pow_pos (clippedAnnulusStep_pos _ _) _)
      (pow_le_pow_right₀ (clippedAnnulusStep_one_le _ _) (Nat.sub_le _ _)))
    (by norm_num)

theorem reciprocal_window (input : ProfileInput call) :
    call.window ⊆ Set.Ici (reciprocal c call.frame)⁻¹ := by
  have h : (reciprocal c call.frame)⁻¹ ≤ lower c call.frame := by
    simpa only [reciprocal, one_div, inv_inv] using
      one_div_le_one_div_of_le (inv_pos.mpr (lower_pos c call.frame))
        (le_max_right 1 (lower c call.frame)⁻¹)
  intro x hx
  exact h.trans ((lower_le_call input).trans hx.1)

theorem prepared_reciprocal_le (input : ProfileInput call) :
    max 1 (call.prepared.lower / 2)⁻¹ ≤ reciprocal c call.frame := by
  apply max_le (reciprocal_one c call.frame)
  have h : (call.prepared.lower / 2)⁻¹ ≤ (lower c call.frame)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (lower_pos c call.frame) (lower_le_call input)
  exact h.trans (le_max_right _ _)

def atomCoefficient (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (N8Source.annulus c frame * reciprocal c frame ^ 2)

theorem atomCoefficient_one (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ atomCoefficient c frame := le_max_left _ _

theorem frozenAmplitude_le (input : ProfileInput call) :
    input.frozenAmplitude ≤ input.amplitude * reciprocal c call.frame :=
  mul_le_mul_of_nonneg_left (prepared_reciprocal_le input)
    (zero_le_one.trans input.amplitude_one_le)

/-- The cost exponent is fixed before the moving amplitude. -/
theorem frozenAtomBudget_le (input : ProfileInput call) :
    input.frozenAtomBudget ≤ atomCoefficient c call.frame * input.amplitude ^ 2 := by
  have ha : 0 ≤ input.amplitude := zero_le_one.trans input.amplitude_one_le
  have hs : 1 ≤ input.amplitude ^ 2 := one_le_pow₀ input.amplitude_one_le
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (atomCoefficient_one c call.frame) hs
  · calc
      2 * call.prepared.upper * input.frozenAmplitude ^ 2 ≤
          N8Source.annulus c call.frame *
            (input.amplitude * reciprocal c call.frame) ^ 2 :=
        mul_le_mul (N8Source.upper_le_annulus input)
          (pow_le_pow_left₀ input.frozenAmplitude_nonneg (frozenAmplitude_le input) 2)
          (sq_nonneg _) (zero_le_one.trans (N8Source.annulus_one_le c call.frame))
      _ = (N8Source.annulus c call.frame * reciprocal c call.frame ^ 2) *
          input.amplitude ^ 2 := by ring
      _ ≤ atomCoefficient c call.frame * input.amplitude ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end N8ScalarWindow

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def firstCentralExponent (side : Bool) : ℝ :=
  call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z -
    idealLogLength call.base (packet.firstFrozenExterior side).val

theorem firstScaleProduct_lower (input : ProfileInput call) (side : Bool) :
    call.base ^ packet.firstCentralExponent side ≤
      N8ScalarWindow.reciprocal c call.frame ^ c.geometry.slots *
        packet.firstScaleProduct side := by
  let B := N8ScalarWindow.reciprocal c call.frame
  have hB : 1 ≤ B := N8ScalarWindow.reciprocal_one c call.frame
  have hprime (i : Fin call.localizedData.geometry.slotCount)
      (_hi : i ∈ Finset.univ \ (packet.firstBranch side).keep) :
      call.base ^ call.originalLength i ≤
        B * (Ideal.absNorm ((packet.firstBranch side).witness.2 i).asIdeal : ℝ) := by
    exact input.localized.primeScale_le_annulus_mul_norm B call.base 0
      (zero_lt_one.trans_le hB) call.base_pos (Set.mem_univ _)
      (N8ScalarWindow.reciprocal_window input) i _
      (Finset.mem_filter.mp (packet.first_witness_slot side i)).1
  have h := (packet.firstBranch side).residualGaussScale_lower call.base call.domain.scale
    call.originalLength (call.originalPlainScale false false)
    (call.originalPlainScale false true)
    (call.node.parameters.n₁ + call.node.parameters.n₂) B c.geometry.slots
    (call.originalPlainScale_pos false false).le (call.originalPlainScale_pos false true).le
    hB call.slots_le (N4.originalPlainScale_product (call := call) false) hprime
  have hsum : (∑ i, call.originalLength i) = call.node.parameters.z :=
    call.domain.total_length.symm
  rw [hsum, packet.firstFrozenExterior_val side] at h
  exact h

/-- The exponent lies in [-1,0]. The annulus loss is at most one
fixed reciprocal factor per original slot, independent of the tilt. -/
theorem firstScaleProduct_power_le (input : ProfileInput call) (side : Bool) :
    packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) ≤
      N8ScalarWindow.reciprocal c call.frame ^ c.geometry.slots *
        call.base ^ (packet.firstCentralExponent side * (-1 + 2 * p.tilt)) := by
  let B := N8ScalarWindow.reciprocal c call.frame ^ c.geometry.slots
  have hB : 1 ≤ B := one_le_pow₀ (N8ScalarWindow.reciprocal_one c call.frame)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hp : -1 + 2 * p.tilt ≤ 0 := by linarith [p.tilt_half]
  have hlower : call.base ^ packet.firstCentralExponent side / B ≤
      packet.firstScaleProduct side := by
    apply (div_le_iff₀ hBpos).mpr
    simpa only [B, mul_comm] using packet.firstScaleProduct_lower input side
  have hpower : B ^ (-(-1 + 2 * p.tilt)) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB
      (show -(-1 + 2 * p.tilt) ≤ (1 : ℝ) by linarith [p.tilt_pos])
  calc
    _ ≤ (call.base ^ packet.firstCentralExponent side / B) ^ (-1 + 2 * p.tilt) :=
      Real.rpow_le_rpow_of_nonpos
        (div_pos (Real.rpow_pos_of_pos call.base_pos _) hBpos) hlower hp
    _ = call.base ^ (packet.firstCentralExponent side * (-1 + 2 * p.tilt)) *
        B ^ (-(-1 + 2 * p.tilt)) := by
      rw [Real.div_rpow (Real.rpow_nonneg call.base_pos.le _) hBpos.le,
        ← Real.rpow_mul call.base_pos.le, div_eq_mul_inv, ← Real.rpow_neg hBpos.le]
    _ ≤ call.base ^ (packet.firstCentralExponent side * (-1 + 2 * p.tilt)) * B :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg call.base_pos.le _)
    _ = _ := mul_comm _ _

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8ScalarWindow.frozenAtomBudget_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstScaleProduct_power_le
