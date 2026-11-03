import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bCommonBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed profile budget for both actual common scalars

The maximal annulus is selected from the original rank schedule.
Its coefficient depends only on the fixed context and source frame;
the moving input enters through its original seminorm amplitude.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace T3b

def commonBudgetBound (c : TargetContext K) (frame : SourceFrame) : ℝ :=
  max 1 (2 * (profileRange c frame).upper *
    (max 1 ((profileRange c frame).lower / 2)⁻¹) ^ 2)

theorem commonBudgetBound_one_le (c : TargetContext K) (frame : SourceFrame) :
    1 ≤ commonBudgetBound c frame := le_max_left _ _

theorem commonBudgetBound_nonneg (c : TargetContext K) (frame : SourceFrame) :
    0 ≤ commonBudgetBound c frame := zero_le_one.trans (commonBudgetBound_one_le c frame)

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace ProfileInput

variable (input : ProfileInput call)

include input in
theorem t3b_commonAnnulus_le :
    2 * call.prepared.upper ≤ 2 * (T3b.profileRange c call.frame).upper := by
  have hmem : 2 * call.prepared.upper ∈ call.window :=
    ⟨by linarith [call.prepared.lower_pos, call.prepared.interval], le_rfl⟩
  exact (call.t3b_window_subset input hmem).2

theorem t3b_frozenAmplitude_le :
    input.frozenAmplitude ≤ input.amplitude *
      max 1 ((T3b.profileRange c call.frame).lower / 2)⁻¹ := by
  have hmem : call.prepared.lower / 2 ∈ call.window :=
    ⟨le_rfl, by linarith [call.prepared.lower_pos, call.prepared.interval]⟩
  have hlower : (T3b.profileRange c call.frame).lower / 2 ≤
      call.prepared.lower / 2 := (call.t3b_window_subset input hmem).1
  have hinv : (call.prepared.lower / 2)⁻¹ ≤
      ((T3b.profileRange c call.frame).lower / 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (div_pos (T3b.profileRange c call.frame).lower_pos (by norm_num)) hlower
  exact mul_le_mul_of_nonneg_left
    (max_le (le_max_left _ _) (hinv.trans (le_max_right _ _)))
    (zero_le_one.trans input.amplitude_one_le)

theorem t3b_frozenAtomBudget_le :
    input.frozenAtomBudget ≤ T3b.commonBudgetBound c call.frame * input.amplitude ^ 2 := by
  have hB := T3b.commonBudgetBound_one_le c call.frame
  have hamp : 1 ≤ input.amplitude ^ 2 := by nlinarith [input.amplitude_one_le]
  change max 1 (2 * call.prepared.upper * input.frozenAmplitude ^ 2) ≤ _
  apply max_le
  · calc
      1 ≤ T3b.commonBudgetBound c call.frame * 1 := by simpa only [mul_one] using hB
      _ ≤ _ := mul_le_mul_of_nonneg_left hamp (T3b.commonBudgetBound_nonneg c call.frame)
  · have hupper : 0 ≤ 2 * (T3b.profileRange c call.frame).upper := by
      have h := (T3b.profileRange c call.frame).lower_pos.trans_le
        (T3b.profileRange c call.frame).interval
      positivity
    calc
      2 * call.prepared.upper * input.frozenAmplitude ^ 2 ≤
          (2 * (T3b.profileRange c call.frame).upper) *
            (input.amplitude * max 1 ((T3b.profileRange c call.frame).lower / 2)⁻¹) ^ 2 :=
        mul_le_mul input.t3b_commonAnnulus_le
          (pow_le_pow_left₀ input.frozenAmplitude_nonneg input.t3b_frozenAmplitude_le 2)
          (sq_nonneg _) hupper
      _ = (2 * (T3b.profileRange c call.frame).upper *
          (max 1 ((T3b.profileRange c call.frame).lower / 2)⁻¹) ^ 2) *
            input.amplitude ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

theorem t3b_frozenAtomBudget_le_one_add :
    input.frozenAtomBudget ≤
      T3b.commonBudgetBound c call.frame * (1 + input.amplitude) ^ 2 := by
  apply input.t3b_frozenAtomBudget_le.trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans input.amplitude_one_le) (by linarith) 2)
    (T3b.commonBudgetBound_nonneg c call.frame)

theorem t3b_frozenAtomBudget_pair_le :
    (input.frozenAtomBudget ^ c.geometry.slots) ^ 2 ≤
      (T3b.commonBudgetBound c call.frame) ^ (2 * c.geometry.slots) *
        (1 + input.amplitude) ^ (4 * c.geometry.slots) := by
  calc
    _ ≤ ((T3b.commonBudgetBound c call.frame * (1 + input.amplitude) ^ 2) ^
        c.geometry.slots) ^ 2 :=
      pow_le_pow_left₀
        (pow_nonneg (zero_le_one.trans input.frozenAtomBudget_one) _)
        (pow_le_pow_left₀ (zero_le_one.trans input.frozenAtomBudget_one)
          input.t3b_frozenAtomBudget_le_one_add _) 2
    _ = _ := by
      simp only [mul_pow, ← pow_mul]
      congr 1 <;> congr 1 <;> omega

end ProfileInput

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem t3bFirstCommonScalar_sq_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (side : Bool) :
    ‖packet.firstCommonScalar side‖ ^ 2 ≤
      (T3b.commonBudgetBound c call.frame * (1 + input.amplitude) ^ 2) ^ c.geometry.slots /
        (Ideal.absNorm (N4.firstFrozenIdeal packet side) : ℝ) := by
  apply (packet.t3b_firstCommonScalar_sq_le input horders side).trans
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (zero_le_one.trans input.frozenAtomBudget_one)
      input.t3b_frozenAtomBudget_le_one_add _) (Nat.cast_nonneg _)

theorem t3bSecondCommonScalar_sq_le (hpacket : packet.Realizes)
    (input : ProfileInput call) (horders : (0, 0) ∈ input.orders)
    (phases : OriginalPhaseData packet) (side : Bool) :
    ‖(packet.firstAtomTable hpacket phases side).commonScalar
        (packet.secondBranch side)‖ ^ 2 ≤
      (T3b.commonBudgetBound c call.frame * (1 + input.amplitude) ^ 2) ^ c.geometry.slots /
        (Ideal.absNorm (N4.secondFrozenIdeal packet side) : ℝ) := by
  apply (packet.t3b_secondCommonScalar_sq_le hpacket input horders phases side).trans
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (zero_le_one.trans input.frozenAtomBudget_one)
      input.t3b_frozenAtomBudget_le_one_add _) (Nat.cast_nonneg _)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileInput.t3b_frozenAtomBudget_pair_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bSecondCommonScalar_sq_le
