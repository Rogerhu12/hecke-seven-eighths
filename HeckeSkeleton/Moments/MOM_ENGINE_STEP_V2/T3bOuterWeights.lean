import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bFirstWeights
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOrbitFibreUniform
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bIndexWeights

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The unchanged first Cauchy scalar and the two Mobius factors

The first selected allowance is cancelled against its original Cauchy
denominator. The two original allowance square roots give the genuine
first common-support weight. Both Mobius norms remain explicit, even
when one is zero. No index weight is replaced or enlarged here.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace T3b

variable {F : FirstPresentation call p}

def selectedAllowance (F : FirstPresentation call p) (key : FirstCauchyKey F) : ℝ :=
  if FirstCauchyKey.side key then
    firstRightAllowance call.base (firstAllowanceTotal F key.1 key.2.1) key.1.val.1 key.1.val.2
  else
    firstLeftAllowance call.base (firstAllowanceTotal F key.1 key.2.1) key.1.val.1 key.1.val.2

theorem selectedAllowance_pos (F : FirstPresentation call p) (key : FirstCauchyKey F) :
    0 < selectedAllowance F key := by
  unfold selectedAllowance
  split_ifs
  · exact firstRightAllowance_pos _ _ call.base_pos _ _
  · exact firstLeftAllowance_pos _ _ call.base_pos _ _

def firstTiltError (F : FirstPresentation call p) (key : FirstCauchyKey F) : ℝ :=
  p.tilt * (idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c)
    key.2.1.val).val - call.workingParameters.m +
      idealLogLength call.base (firstActiveRadical key.1.val.1 key.1.val.2))

/-- Preserve the original Mobius norm through Cauchy's selected side. -/
theorem firstCauchy_outer_mul_allowance_mobius
    (hF : F.Realizes) (key : FirstCauchyKey F) (N : F.source.Normalization) :
    let NL := N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
    let NR := N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
    FirstCauchyKey.outer key N * (if FirstCauchyKey.side key then NR else NL) ≤
      ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
        (firstRowMajorant F key.1 key.2.1 * Real.sqrt NL * Real.sqrt NR / 2) := by
  dsimp only
  let NL := N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  let NR := N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
  have hden : 0 < if FirstCauchyKey.side key then NR else NL := by
    split_ifs
    · exact N.right_pos _ _ _ _
    · exact N.left_pos _ _ _ _
  have hW : 0 ≤ (FirstCauchyKey.piece key).rowBound * Real.sqrt NL * Real.sqrt NR / 2 := by
    exact div_nonneg (mul_nonneg
      (mul_nonneg (FirstCauchyKey.piece key).rowBound_nonneg (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (by norm_num)
  unfold FirstCauchyKey.outer
  rw [hF.fiber, Nat.cast_one, one_mul, div_mul_cancel₀ _ hden.ne']
  calc
    _ ≤ (‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ * 1) *
        ((FirstCauchyKey.piece key).rowBound * Real.sqrt NL * Real.sqrt NR / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (fixed_phase_coefficient_norm PUnit (fun _ => (1 : Circle))
          (FirstCauchyKey.character key)) (norm_nonneg _)) hW
    _ ≤ _ := by
      rw [mul_one]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (realizedFirst_rowBound_le F hF key.1 key.2.1)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- The exact scalar identity isolates only the original positive
Mellin tilt. The unchanged parent width is used on both sides. -/
theorem first_allowance_tilt_identity (hF : F.Realizes) (key : FirstCauchyKey F) :
    firstRowMajorant F key.1 key.2.1 *
      Real.sqrt (firstLeftAllowance call.base
        (firstAllowanceTotal F key.1 key.2.1) key.1.val.1 key.1.val.2) *
      Real.sqrt (firstRightAllowance call.base
        (firstAllowanceTotal F key.1 key.2.1) key.1.val.1 key.1.val.2) *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) /
        call.parentNormalizer =
      orbitalFieldFactor K * firstCommonWeight call.base key.1.val.1 key.1.val.2 *
        call.base ^ firstTiltError F key := by
  rw [realizedFirst_rowMajorant_eq_rpow F hF]
  unfold firstLeftAllowance firstRightAllowance firstCommonWeight firstRowExponent
    firstAllowanceTotal firstTiltError Call.parentNormalizer
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul call.base_pos.le]
  have hw : call.node.parameters.m + call.node.parameters.q =
      call.workingParameters.m + call.workingParameters.q := by
    simp only [Call.workingParameters]
    ring
  rw [hw]
  rw [div_eq_mul_inv, ← Real.rpow_neg call.base_pos.le]
  simp only [mul_assoc, ← Real.rpow_add call.base_pos]
  congr 1
  congr 1
  ring

end T3b

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem t3b_outer_allowance_mobius (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    let key := family.index i
    (family.source i).outerWeight * T3b.selectedAllowance F key *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) /
        call.parentNormalizer ≤
      (orbitalFieldFactor K / 2) * ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
        firstCommonWeight call.base key.1.val.1 key.1.val.2 *
        call.base ^ T3b.firstTiltError F key := by
  dsimp only
  have h := T3b.firstCauchy_outer_mul_allowance_mobius hF (family.index i) family.normalization
  simp only [hfamily.leftAllowance, hfamily.rightAllowance] at h
  have h' : (family.source i).outerWeight * T3b.selectedAllowance F (family.index i) ≤
      ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual (family.index i)).val : ℂ)‖ *
        (T3b.firstRowMajorant F (family.index i).1 (family.index i).2.1 *
          Real.sqrt (firstLeftAllowance call.base
            (T3b.firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
            (family.index i).1.val.1 (family.index i).1.val.2) *
          Real.sqrt (firstRightAllowance call.base
            (T3b.firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
            (family.index i).1.val.1 (family.index i).1.val.2) / 2) := by
    rw [hfamily.outer i]
    exact h
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right h' (Real.rpow_nonneg call.base_pos.le _))
    call.parentNormalizer_pos.le).trans_eq
  calc
    _ = (‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual (family.index i)).val : ℂ)‖ / 2) *
        (T3b.firstRowMajorant F (family.index i).1 (family.index i).2.1 *
          Real.sqrt (firstLeftAllowance call.base
            (T3b.firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
            (family.index i).1.val.1 (family.index i).1.val.2) *
          Real.sqrt (firstRightAllowance call.base
            (T3b.firstAllowanceTotal F (family.index i).1 (family.index i).2.1)
            (family.index i).1.val.1 (family.index i).1.val.2) *
          call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) /
            call.parentNormalizer) := by ring
    _ = _ := by rw [T3b.first_allowance_tilt_identity hF]; ring

theorem t3b_outer_allowance_radical (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    let key := family.index i
    (family.source i).outerWeight * T3b.selectedAllowance F key *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) /
        call.parentNormalizer ≤
      (orbitalFieldFactor K / 2) * ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ *
        (1 / (Ideal.absNorm (commonRadical key.1.val.1 key.1.val.2) : ℝ)) *
        call.base ^ T3b.firstTiltError F key := by
  dsimp only
  apply (family.t3b_outer_allowance_mobius hF hfamily i).trans
  have hD : (family.index i).1.val.1 ≠ 0 := by
    rw [← (F.source.block (family.index i).1).common_left]
    exact (primePowerProduct _ _).property.1
  have hE : (family.index i).1.val.2 ≠ 0 := by
    rw [← (F.source.block (family.index i).1).common_right]
    exact (primePowerProduct _ _).property.1
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (firstCommonWeight_le_radical call.base call.domain.scale _ _ hD hE
        (F.source.block (family.index i).1).common_support_eq)
      (mul_nonneg (div_nonneg (orbitalFieldFactor_nonneg K) (by norm_num)) (norm_nonneg _)))
    (Real.rpow_nonneg call.base_pos.le _)

end FirstCauchyFamily

namespace RawLeafPacket

theorem t3b_leaf_outer_weight_le (packet : RawLeafPacket call p) :
    packet.leaf.weight ≤ packet.second.physical.outerWeight * (packet.second.stage.fiber : ℝ) *
      ‖(UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)‖ := by
  change (packet.second.physical.outerWeight * (packet.second.stage.fiber : ℝ)) *
    (‖(UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)‖ *
      ‖fixedPhaseCoefficient PUnit (fun _ => (1 : Circle)) packet.allocation.2.1‖) ≤ _
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (fixed_phase_coefficient_norm PUnit (fun _ => (1 : Circle)) packet.allocation.2.1)
      (norm_nonneg (UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)))
    (mul_nonneg packet.second.physical.outerWeight_nonneg
      (Nat.cast_nonneg packet.second.stage.fiber))
  simpa only [mul_one] using h

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.t3b_outer_allowance_radical
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_leaf_outer_weight_le
