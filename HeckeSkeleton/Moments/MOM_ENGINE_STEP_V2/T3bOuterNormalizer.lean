import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPoolOuter
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bFirstColumnBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original outer normalization on the same arithmetic index

The first common radical and its original Mobius factor are transported
through the direct, main and valuation-error sources. The pool allowance
is exactly the existing index prefactor. The second physical fibre is
bounded by the fixed constant proved from these same source rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
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
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace FirstCoordinates

def t3bIndexFactor (first : FirstCoordinates call) : ℝ :=
  (1 / (Ideal.absNorm (commonRadical first.selected.val first.opposite.val) : ℝ)) *
    ‖(moebius first.residualDivisor.val : ℂ)‖

theorem t3bIndexFactor_nonneg (first : FirstCoordinates call) :
    0 ≤ first.t3bIndexFactor := by
  unfold t3bIndexFactor
  positivity

end FirstCoordinates

namespace FirstCauchyFamily

theorem t3b_first_commonRadical (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (i : Fin family.count) :
    commonRadical (family.source i).first.selected.val (family.source i).first.opposite.val =
      commonRadical (family.index i).1.val.1 (family.index i).1.val.2 := by
  rw [hfamily.selected i, hfamily.opposite i]
  split_ifs
  · exact commonRadical_comm _ _
  · rfl

theorem t3b_outer_first_factor (family : FirstCauchyFamily F)
    (hF : F.Realizes) (hfamily : family.Realizes) (i : Fin family.count) :
    (family.source i).outerWeight * (family.source i).first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) / call.parentNormalizer ≤
      (orbitalFieldFactor K / 2) * (family.source i).first.t3bIndexFactor *
        call.base ^ T3b.firstTiltError F (family.index i) := by
  rw [family.t3b_selectedAllowance_eq hfamily i]
  have h := family.t3b_outer_allowance_radical hF hfamily i
  apply h.trans_eq
  rw [FirstCoordinates.t3bIndexFactor, family.t3b_first_commonRadical hfamily i,
    hfamily.residual i]
  ring

end FirstCauchyFamily

namespace PoolExpansion

theorem t3b_first_indexFactor (expansion : PoolExpansion family)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (expansion.source i).first.t3bIndexFactor =
      (family.source (expansion.t3bFirstIndex i)).first.t3bIndexFactor := by
  have h := expansion.t3b_first_scalarCoordinates hexpansion i
  have hs : (expansion.source i).first.selected.val =
      (family.source (expansion.t3bFirstIndex i)).first.selected.val :=
    congrArg Prod.fst h
  have ho : (expansion.source i).first.opposite.val =
      (family.source (expansion.t3bFirstIndex i)).first.opposite.val :=
    congrArg (fun x => x.2.1) h
  have hr : (expansion.source i).first.residualDivisor.val =
      (family.source (expansion.t3bFirstIndex i)).first.residualDivisor.val :=
    congrArg (fun x => x.2.2.2) h
  unfold FirstCoordinates.t3bIndexFactor
  rw [hs, ho, hr]

theorem t3b_outer_first_factor (expansion : PoolExpansion family)
    (hF : F.Realizes) (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).outerWeight * (expansion.source i).first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) *
        call.base ^ ((expansion.source i).first.tag.movingLength call.base +
          (expansion.source i).first.tag.poolLength (recipeInductionSigma c)) /
        call.parentNormalizer ≤
      (orbitalFieldFactor K / 2) * expansion.indexPrefactor i *
        (expansion.source i).first.t3bIndexFactor *
        call.base ^ T3b.firstTiltError F (family.index (expansion.t3bFirstIndex i)) := by
  calc
    _ = ((expansion.source i).outerWeight *
        call.base ^ ((expansion.source i).first.tag.movingLength call.base +
          (expansion.source i).first.tag.poolLength (recipeInductionSigma c))) *
        (expansion.source i).first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) / call.parentNormalizer := by ring
    _ = ((family.source (expansion.t3bFirstIndex i)).outerWeight *
        (family.source (expansion.t3bFirstIndex i)).first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) / call.parentNormalizer) * expansion.indexPrefactor i := by
      rw [expansion.t3b_outer_poolAllowance hfamily hexpansion i,
        expansion.t3b_first_allowance hexpansion i]
      ring
    _ ≤ ((orbitalFieldFactor K / 2) *
        (family.source (expansion.t3bFirstIndex i)).first.t3bIndexFactor *
        call.base ^ T3b.firstTiltError F (family.index (expansion.t3bFirstIndex i))) *
        expansion.indexPrefactor i :=
      mul_le_mul_of_nonneg_right (family.t3b_outer_first_factor hF hfamily _)
        (expansion.t3b_indexPrefactor_nonneg i)
    _ = _ := by rw [expansion.t3b_first_indexFactor hexpansion i]; ring

end PoolExpansion

namespace RawFamily

theorem t3b_outer_scalar_to_index
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry) (j : Fin raw.count)
    (value coefficient scalarLoss : ℝ) (hcoefficient : 0 ≤ coefficient)
    (hvalue : value ≤
      coefficient * (raw.packet j).second.physical.first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) *
        call.base ^ ((raw.packet j).second.physical.first.tag.movingLength call.base +
          (raw.packet j).second.physical.first.tag.poolLength (recipeInductionSigma c)) /
        (Ideal.absNorm (commonRadical (raw.packet j).key.1.val.1
          (raw.packet j).key.1.val.2) : ℝ) * call.base ^ scalarLoss) :
    (raw.packet j).leaf.weight * value / call.parentNormalizer ≤
      (coefficient * (orbitalFieldFactor K / 2) * T3b.physicalOrbitFibreConstant c p) *
        trace.expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ (T3b.firstTiltError trace.first
          (trace.cauchy.index (trace.expansion.t3bFirstIndex (raw.sourceIndex j))) + scalarLoss) := by
  let packet := raw.packet j
  let first := packet.second.physical.first
  let i := raw.sourceIndex j
  let Q : ℝ := Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hphysical : packet.second.physical = trace.expansion.source i := by
    change (trace.second.source i).physical = trace.expansion.source i
    exact htrace.second.physical i
  have hweight : packet.leaf.weight ≤ packet.second.physical.outerWeight *
      T3b.physicalOrbitFibreConstant c p * ‖(moebius packet.allocation.1.val : ℂ)‖ :=
    packet.t3b_leaf_outer_weight_le.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (raw.t3b_secondFiber_uniform trace htrace j)
          packet.second.physical.outerWeight_nonneg) (norm_nonneg _))
  have houter : packet.second.physical.outerWeight * first.t3bAllowance *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z)) *
      call.base ^ (first.tag.movingLength call.base +
        first.tag.poolLength (recipeInductionSigma c)) / call.parentNormalizer ≤
      (orbitalFieldFactor K / 2) * trace.expansion.indexPrefactor i *
        first.t3bIndexFactor * call.base ^ T3b.firstTiltError trace.first
          (trace.cauchy.index (trace.expansion.t3bFirstIndex i)) := by
    dsimp only [first]
    rw [hphysical]
    exact trace.expansion.t3b_outer_first_factor htrace.first htrace.cauchy htrace.expansion i
  have hright : 0 ≤ coefficient * first.t3bAllowance *
      call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z)) *
      call.base ^ (first.tag.movingLength call.base +
        first.tag.poolLength (recipeInductionSigma c)) / Q * call.base ^ scalarLoss := by
    have ha := first.t3bAllowance_pos.le
    have hz := call.base_pos.le
    positivity
  have hremaining : 0 ≤ coefficient * T3b.physicalOrbitFibreConstant c p *
      ‖(moebius packet.allocation.1.val : ℂ)‖ / Q * call.base ^ scalarLoss := by
    have hf := T3b.physicalOrbitFibreConstant_nonneg (c := c) (p := p)
    have hz := call.base_pos.le
    positivity
  calc
    _ ≤ packet.leaf.weight *
        (coefficient * first.t3bAllowance *
          call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
            call.workingParameters.z)) *
          call.base ^ (first.tag.movingLength call.base +
            first.tag.poolLength (recipeInductionSigma c)) / Q * call.base ^ scalarLoss) /
        call.parentNormalizer :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hvalue packet.leaf.weight_nonneg) call.parentNormalizer_pos.le
    _ ≤ (packet.second.physical.outerWeight * T3b.physicalOrbitFibreConstant c p *
          ‖(moebius packet.allocation.1.val : ℂ)‖) *
        (coefficient * first.t3bAllowance *
          call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
            call.workingParameters.z)) *
          call.base ^ (first.tag.movingLength call.base +
            first.tag.poolLength (recipeInductionSigma c)) / Q * call.base ^ scalarLoss) /
        call.parentNormalizer :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hweight hright)
        call.parentNormalizer_pos.le
    _ = (packet.second.physical.outerWeight * first.t3bAllowance *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z)) *
        call.base ^ (first.tag.movingLength call.base +
          first.tag.poolLength (recipeInductionSigma c)) / call.parentNormalizer) *
        (coefficient * T3b.physicalOrbitFibreConstant c p *
          ‖(moebius packet.allocation.1.val : ℂ)‖ / Q * call.base ^ scalarLoss) := by ring
    _ ≤ ((orbitalFieldFactor K / 2) * trace.expansion.indexPrefactor i *
        first.t3bIndexFactor * call.base ^ T3b.firstTiltError trace.first
          (trace.cauchy.index (trace.expansion.t3bFirstIndex i))) *
        (coefficient * T3b.physicalOrbitFibreConstant c p *
          ‖(moebius packet.allocation.1.val : ℂ)‖ / Q * call.base ^ scalarLoss) :=
      mul_le_mul_of_nonneg_right houter hremaining
    _ = _ := by
      simp only [commonIndexFactor, innerDivisor, FirstCoordinates.t3bIndexFactor,
        Real.rpow_add call.base_pos, packet, first, i, Q]
      ring

end RawFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_outer_scalar_to_index
