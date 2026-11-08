module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPacketNormalizer
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bOuterNormalizer
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUniformBudget

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The exceptional normalizer and the original arithmetic index

The actual point scalar is paid by the actual first allowance. Both
Mobius factors, both common radicals, and the single pool prefactor
are retained. Only a fixed physical-fibre constant and the two original
positive Mellin tilts remain outside that same arithmetic index.
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

namespace T3b

def normalizerLoss (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  (10 + recipeInductionSigma c / 4) * p.loss +
    (8 + recipeInductionSigma c / 4) * p.loss

def commonNormalizerCoefficient (c : TargetContext K) (p : SourceParameters c)
    (frame : SourceFrame) (C : ℝ) : ℝ :=
  C ^ 2 * profileAnnulus c frame ^ (4 * c.geometry.slots) *
    (orbitalFieldFactor K) ^ 2 / 2 * physicalOrbitFibreConstant c p

theorem commonNormalizerCoefficient_nonneg (c : TargetContext K)
    (p : SourceParameters c) (frame : SourceFrame) (C : ℝ) :
    0 ≤ commonNormalizerCoefficient c p frame C := by
  have hA := zero_le_one.trans (profileAnnulus_one_le c frame)
  have hF := physicalOrbitFibreConstant_nonneg (c := c) (p := p)
  unfold commonNormalizerCoefficient
  positivity

end T3b

namespace RawFamily

theorem t3b_normalizer_from_common_bounds
    (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (hgeometry : geometry.Realizes)
    (raw : RawFamily geometry) (hraw : raw.Realizes) (j : Fin raw.count)
    (input : ProfileInput call) (phases : OriginalPhaseData (raw.packet j)) (side : Bool)
    (hannulus : T3b.firstColumnAnnulus c call.frame ≤ call.base)
    (C : ℝ) (hC : 0 ≤ C)
    (hfirst : ∀ s, ‖(raw.packet j).firstCommonScalar s‖ ^ 2 ≤
      C / (Ideal.absNorm (N4.firstFrozenIdeal (raw.packet j) s) : ℝ))
    (hsecond : ∀ s,
      ‖((raw.packet j).firstAtomTable (raw.packet_realizes trace htrace hgeometry hraw j)
        phases s).commonScalar ((raw.packet j).secondBranch s)‖ ^ 2 ≤
      C / (Ideal.absNorm (N4.secondFrozenIdeal (raw.packet j) s) : ℝ)) :
    (raw.packet j).leaf.weight *
        (raw.packet j).t3bPointScalar (raw.packet_realizes trace htrace hgeometry hraw j)
          phases side * call.base ^ (raw.packet j).t3bNominalNorm side /
        call.parentNormalizer ≤
      T3b.commonNormalizerCoefficient c p call.frame C *
        trace.expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ T3b.normalizerLoss c p := by
  let packet := raw.packet j
  let hp := raw.packet_realizes trace htrace hgeometry hraw j
  let A := call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z
  let Cpair := C * C * T3b.profileAnnulus c call.frame ^ (4 * c.geometry.slots) *
    orbitalFieldFactor K
  have hCpair : 0 ≤ Cpair := by
    have hA := zero_le_one.trans (T3b.profileAnnulus_one_le c call.frame)
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hC) (pow_nonneg hA _))
      (orbitalFieldFactor_nonneg K)
  have hpoint := packet.t3bPointScalar_nominal_le hp input phases side C C hC hC hfirst hsecond
  have houter := raw.t3b_outer_scalar_to_index trace htrace j
    (packet.t3bPointScalar hp phases side * call.base ^ packet.t3bNominalNorm side)
    Cpair (4 * p.tilt * A) hCpair (by
      simpa only [Cpair, A, RawLeafPacket.secondIdeal, Bool.false_eq_true, if_false, if_true,
        Call.workingParameters] using hpoint)
  have hfirstTilt := trace.first.t3b_firstTilt_le htrace.first input
    (trace.cauchy.index (trace.expansion.t3bFirstIndex (raw.sourceIndex j))).1
    (trace.cauchy.index (trace.expansion.t3bFirstIndex (raw.sourceIndex j))).2.1 hannulus
  have hscalarTilt := T3b.original_scalar_tilt_le call p
  have hexp : T3b.firstTiltError trace.first
      (trace.cauchy.index (trace.expansion.t3bFirstIndex (raw.sourceIndex j))) +
      4 * p.tilt * A ≤ T3b.normalizerLoss c p := by
    unfold T3b.normalizerLoss
    apply add_le_add
    · simpa only [T3b.firstTiltError, mul_comm p.loss] using hfirstTilt
    · exact hscalarTilt
  have hcoeff : Cpair * (orbitalFieldFactor K / 2) * T3b.physicalOrbitFibreConstant c p =
      T3b.commonNormalizerCoefficient c p call.frame C := by
    unfold Cpair T3b.commonNormalizerCoefficient
    ring
  calc
    _ = packet.leaf.weight *
        (packet.t3bPointScalar hp phases side * call.base ^ packet.t3bNominalNorm side) /
        call.parentNormalizer := by ring
    _ ≤ (Cpair * (orbitalFieldFactor K / 2) * T3b.physicalOrbitFibreConstant c p) *
        trace.expansion.indexPrefactor (raw.sourceIndex j) * raw.commonIndexFactor j *
        call.base ^ (T3b.firstTiltError trace.first
          (trace.cauchy.index (trace.expansion.t3bFirstIndex (raw.sourceIndex j))) +
            4 * p.tilt * A) := houter
    _ ≤ _ := by
      rw [hcoeff]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexp)
        (mul_nonneg
          (mul_nonneg (T3b.commonNormalizerCoefficient_nonneg c p call.frame C)
            (trace.expansion.t3b_indexPrefactor_nonneg _))
          (raw.t3b_commonIndexFactor_nonneg j))

end RawFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_normalizer_from_common_bounds
