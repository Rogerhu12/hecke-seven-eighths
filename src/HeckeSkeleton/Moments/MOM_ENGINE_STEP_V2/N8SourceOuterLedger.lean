module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourcePoolMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroFirstMass
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedLeafWeights

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual first Cauchy scalar in the normalized source ledger

The shared first-chart theorem bounds the original weight supremum.
The selected allowance cancels its original denominator; both allowance
square roots and the active norm pay the first common radical. The
original first Möbius norm remains exactly once.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Global Tasks.SecondZeroProof

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace PhysicalSource

def firstBaseExponent (source : PhysicalSource call p) : ℝ :=
  idealLogLength call.base (firstActiveRadical source.first.selected.val source.first.opposite.val) +
    idealLogLength call.base source.first.complementary.val -
    idealLogLength call.base source.first.selected.val +
    firstAllowance (idealLogLength call.base source.first.selected.val)
      (idealLogLength call.base source.first.opposite.val)
      (idealLogLength call.base (firstActiveRadical source.first.selected.val
        source.first.opposite.val)) - call.workingParameters.m

def poolIndexAllowance (source : PhysicalSource call p) : ℝ :=
  call.base ^ (source.first.tag.movingLength call.base +
    source.first.tag.poolLength (recipeInductionSigma c))

def firstLedgerExponent (source : PhysicalSource call p) : ℝ :=
  source.firstBaseExponent + source.first.tag.movingLength call.base +
    source.first.tag.poolLength (recipeInductionSigma c)

theorem firstBasePower_eq (source : PhysicalSource call p) :
    call.base ^ source.firstBaseExponent =
      sourceSideAllowance source * call.base ^
        (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) /
          call.parentNormalizer := by
  unfold sourceSideAllowance secondSideAllowance firstBaseExponent Call.parentNormalizer
  rw [← Real.rpow_add call.base_pos, ← Real.rpow_sub call.base_pos]
  congr 1
  rw [← N8Source.working_width call]
  ring

theorem firstLedgerPower_eq (source : PhysicalSource call p) :
    call.base ^ source.firstLedgerExponent =
      call.base ^ source.firstBaseExponent * source.poolIndexAllowance := by
  unfold firstLedgerExponent poolIndexAllowance
  rw [← Real.rpow_add call.base_pos]
  congr 1
  ring

end PhysicalSource

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

theorem commonRadical_eq_key (hf : family.Realizes) (i : Fin family.count) :
    commonRadical (family.source i).first.selected.val (family.source i).first.opposite.val =
      commonRadical (family.index i).1.val.1 (family.index i).1.val.2 := by
  rw [hf.selected i, hf.opposite i]
  cases hs : FirstCauchyKey.side (family.index i) <;>
    simp only [hs, Bool.false_eq_true, if_false, if_true, N8Source.commonRadical_comm]

private theorem normalized_outer_scalar (fiber mobius phase rows normalizer : ℝ)
    (hfiber : fiber = 1) (hphase : phase = 1) :
    (fiber * mobius * phase * (rows / 2)) / normalizer =
      (mobius / 2) * (rows / normalizer) := by
  rw [hfiber, hphase]
  ring

set_option maxHeartbeats 1000000 in
/-- T1/T2 supply the primitive chart and row-allowance estimates.
This consumer retains the original first Möbius norm and radical. -/
theorem outer_sideAllowance_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count) :
    (family.source i).outerWeight * sourceSideAllowance (family.source i) /
        call.parentNormalizer ≤
      orbitalFieldFactor K * call.base ^
        (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
          2 * N8Source.columnExponent c * p.tilt) *
        (family.source i).firstCommonFactor := by
  let key := family.index i
  let amp : ℝ := orbitalFieldFactor K * call.base ^
    (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
      2 * N8Source.columnExponent c * p.tilt)
  have hamp : 0 ≤ amp := mul_nonneg (orbitalFieldFactor_nonneg K)
    (Real.rpow_nonneg call.base_pos.le _)
  have hrow := first_row_allowance_le F family hf key.1 key.2.1
    (FirstCauchyKey.residual key) (FirstCauchyKey.character key) amp
    (first_weightBound_normalized F hF (N8Source.columnExponent c)
      (N8Source.first_source_norm input large F hF) key.1 key.2.1)
  have hD : key.1.val.1 ≠ 0 := by
    rw [← (FirstCauchyKey.block key).common_left]
    exact (primePowerProduct (FirstCauchyKey.block key).primes
      (FirstCauchyKey.block key).leftMultiplicity).property.1
  have hE : key.1.val.2 ≠ 0 := by
    rw [← (FirstCauchyKey.block key).common_right]
    exact (primePowerProduct (FirstCauchyKey.block key).primes
      (FirstCauchyKey.block key).rightMultiplicity).property.1
  have hrad := mul_le_mul_of_nonneg_left
    (firstCommonWeight_le_radical call.base call.domain.scale key.1.val.1 key.1.val.2
      hD hE key.common_support_eq) hamp
  have hmu := mul_le_mul_of_nonneg_left (hrow.trans hrad)
    (div_nonneg (norm_nonneg (UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ))
      (by norm_num : (0 : ℝ) ≤ 2))
  have he : (family.source i).outerWeight * sourceSideAllowance (family.source i) /
        call.parentNormalizer =
      (‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ / 2) *
        ((FirstCauchyKey.piece key).rowBound *
          Real.sqrt (family.normalization.left key.1 key.2.1
            (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) *
          Real.sqrt (family.normalization.right key.1 key.2.1
            (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) /
          call.parentNormalizer) := by
    have hsource :
        (family.source i).outerWeight * sourceSideAllowance (family.source i) =
          FirstCauchyKey.outer key family.normalization *
            firstSideAllowance key family.normalization :=
      congrArg₂ (fun outer allowance : ℝ => outer * allowance) (hf.outer i)
        (first_family_side_allowance family hf i)
    have hfiber : (F.source.fiber : ℝ) = 1 := by
      simpa only [Nat.cast_one] using
        congrArg (fun n : ℕ => (n : ℝ)) hF.fiber
    have hphase :
        ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle))
          (FirstCauchyKey.character key)‖ = (1 : ℝ) := by
      rw [punitPhaseCoefficient_eq_one, norm_one]
    exact (congrArg (fun scalar : ℝ => scalar / call.parentNormalizer)
      (hsource.trans (first_key_outer_mul_allowance key family.normalization))).trans
        (normalized_outer_scalar (F.source.fiber : ℝ)
          ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖
          ‖fixedPhaseCoefficient PUnit.{1} (fun _ => (1 : Circle))
            (FirstCauchyKey.character key)‖
          ((FirstCauchyKey.piece key).rowBound *
            Real.sqrt (family.normalization.left key.1 key.2.1
              (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) *
            Real.sqrt (family.normalization.right key.1 key.2.1
              (FirstCauchyKey.residual key) (FirstCauchyKey.character key)))
          call.parentNormalizer hfiber hphase)
  rw [he]
  apply hmu.trans
  have hhalf : ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ / 2 ≤
      ‖(UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)‖ := by
    nlinarith [norm_nonneg (UniqueFactorizationMonoid.moebius (FirstCauchyKey.residual key).val : ℂ)]
  apply (mul_le_mul_of_nonneg_right hhalf
    (mul_nonneg hamp (one_div_nonneg.mpr (Nat.cast_nonneg _)))).trans_eq
  unfold PhysicalSource.firstCommonFactor
  rw [family.commonRadical_eq_key hf i, hf.residual i]
  dsimp only [amp, key]
  ring

theorem first_base_ledger_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes) (i : Fin family.count) :
    (family.source i).outerWeight * call.base ^ (family.source i).firstBaseExponent ≤
      orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        (family.source i).firstCommonFactor := by
  have h := mul_le_mul_of_nonneg_right
    (family.outer_sideAllowance_le input large hF hf i)
    (Real.rpow_nonneg call.base_pos.le
      (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)))
  calc
    _ = ((family.source i).outerWeight * sourceSideAllowance (family.source i) /
        call.parentNormalizer) * call.base ^
        (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) := by
      rw [(family.source i).firstBasePower_eq]
      ring
    _ ≤ _ := h
    _ = _ := by
      have he : (call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z + 2 * N8Source.columnExponent c * p.tilt) +
          (-(call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)) =
            2 * N8Source.columnExponent c * p.tilt := by ring
      calc
        _ = orbitalFieldFactor K *
            (call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
              call.workingParameters.z + 2 * N8Source.columnExponent c * p.tilt) *
            call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
              call.workingParameters.z))) * (family.source i).firstCommonFactor := by ring
        _ = _ := by rw [← Real.rpow_add call.base_pos, he]

end FirstCauchyFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyFamily.first_base_ledger_le
