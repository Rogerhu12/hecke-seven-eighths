import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOriginalGeometry

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed exponent for the original second frequency ideal

Restoring the actual gcd and nonunit radical cancels their two
logarithmic subtractions from the S5 row window. The original retained
scale is at least one, and every original first extraction and
enlargement has nonnegative length. The remaining exponent is therefore
bounded before the call, row, common pair and frequency class.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace FirstCauchyFamily

theorem t3b_retainedScale_one (family : FirstCauchyFamily F)
    (hfamily : family.Realizes) (i : Fin family.count) :
    1 ≤ (family.source i).first.retainedScale := by
  rw [hfamily.retained i]
  exact le_max_left _ _

end FirstCauchyFamily

namespace PoolExpansion

theorem t3b_retainedScale_one (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    1 ≤ (expansion.source i).first.retainedScale := by
  cases expansion with
  | direct => exact family.t3b_retainedScale_one hfamily i
  | pooled P count index source =>
    have hfirst := family.t3b_retainedScale_one hfamily (index i).1
    cases htag : (index i).2 with
    | inl u =>
      have ho : P.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, he⟩
      change 1 ≤ (source i).first.retainedScale
      simpa only [he] using hfirst
    | inr qe =>
      have ho : P.ErrorOrigin (index i).1 qe.1 qe.2 (source i) := by
        simpa only [PoolPresentation.Origin, htag] using hexpansion.2.2 i
      rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _, _, _⟩
      change 1 ≤ (source i).first.retainedScale
      rw [hs]
      exact hfirst

end PoolExpansion

namespace T3b

def secondOriginalRowExponentBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  4 + recipeInductionSigma c / 8 + 12 * p.loss

theorem secondOriginalRowExponentBound_nonneg :
    0 ≤ secondOriginalRowExponentBound c p := by
  have hs := (recipeInduction_budget (c := c)).1
  have hp := p.loss_pos
  unfold secondOriginalRowExponentBound
  positivity

theorem nominal_frequencyCenter_le
    (G : OriginalNominalGeometry (K := K) call.workingParameters call.base
      (recipeInductionSigma c)) (hretained : 1 ≤ G.retainedScale) :
    G.frequencyCenter ≤
      2 * (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z) := by
  have hc : 0 ≤ G.skeleton.c :=
    idealLogLength_nonneg call.base call.domain.scale _ (nonZeroDivisors.coe_ne_zero _)
  have hw : 0 ≤ G.skeleton.w := G.tag.removedLength_nonneg call.base call.domain.scale
  have hk : 0 ≤ G.skeleton.Krow :=
    div_nonneg (Real.log_nonneg hretained) (Real.log_pos call.domain.scale).le
  have hpad : 0 ≤ G.tag.padding (recipeInductionSigma c) := by
    have hs := (recipeInduction_budget (c := c)).1
    cases G.tag <;> simp only [OriginalNominalTag.padding] <;> positivity
  have hg : 0 ≤ G.skeleton.g := add_nonneg (le_max_right _ _) hpad
  change 2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w) -
    G.skeleton.Krow - G.skeleton.g ≤ 2 * G.skeleton.A
  linarith

end T3b

namespace RawLeafPacket

theorem t3b_retainedScale_one (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    1 ≤ packet.second.physical.first.retainedScale := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  change 1 ≤ (trace.second.source (raw.index j).val.1.1).physical.first.retainedScale
  rw [htrace.second.physical]
  exact trace.expansion.t3b_retainedScale_one htrace.cauchy htrace.expansion _

theorem t3b_originalRow_norm_uniform (packet : RawLeafPacket call p)
    (hpacket : packet.Realizes) (h : packet.R.live) :
    (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) ≤
      call.base ^ T3b.secondOriginalRowExponentBound c p := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  let packet := raw.packet j
  let G := packet.nominal false
  have hpacket : packet.Realizes := raw.packet_realizes trace htrace hgeometry hraw j
  have hG := hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)
  have hgcd : gcd (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
        (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val =
      gcd G.ideals.second.val G.ideals.secondOpposite.val := by
    rw [packet.block.common_left, packet.block.common_right]
    rw [hG.second false, hG.secondOpposite false]
    rfl
  have hnonunit : (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val =
      G.ideals.nonunitPart.val := (hG.nonunitPart false h).symm
  have hnorm := packet.t3b_originalRow_norm_le h hpacket false
  rw [hgcd, hnonunit,
    ← rpow_idealLogLength call.base call.domain.scale
      (gcd G.ideals.second.val G.ideals.secondOpposite.val)
      (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
    ← rpow_idealLogLength call.base call.domain.scale G.ideals.nonunitPart.val
      (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart),
    ← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos] at hnorm
  have hexp : G.skeleton.g₂ + G.skeleton.V +
      (G.skeleton.nominalRow + 12 * p.loss) = G.frequencyCenter + 12 * p.loss := by
    dsimp only [NominalChildGeometry.nominalRow, OriginalNominalGeometry.frequencyCenter]
    ring
  change (Ideal.absNorm (packet.R.originalIdeal h.val).val : ℝ) ≤
    call.base ^ (G.skeleton.g₂ + G.skeleton.V +
      (G.skeleton.nominalRow + 12 * p.loss)) at hnorm
  rw [hexp] at hnorm
  apply hnorm.trans
  apply Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
  have hretained : 1 ≤ G.retainedScale := by
    rw [hG.retainedScale false]
    exact packet.t3b_retainedScale_one hpacket
  have hcenter := T3b.nominal_frequencyCenter_le G hretained
  have hA := call.t3b_totalLength_le
  unfold T3b.secondOriginalRowExponentBound
  linarith

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_originalRow_norm_uniform
