import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bPointwiseData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bFrozenAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bRowAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScalarArithmetic

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual exceptional point scalar at its nominal normalization

The two original common scalars, the actual second row amplitude and
the original common correlation are combined with the same raw-mass
normalizer used in the pointwise source estimate. Exact S5 norm
coordinates leave the selected first allowance, the original pool
factor and one inverse second common radical. No aggregate terminal
bound or replacement scalar is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p) (hpacket : packet.Realizes)

theorem t3b_secondRadical_rpow (side : Bool) :
    call.base ^ (packet.nominal side).secondRadical =
      (Ideal.absNorm (commonRadical (packet.secondIdeal false) (packet.secondIdeal true)) : ℝ) := by
  rw [OriginalNominalGeometry.secondRadical,
    packet.t3b_nominal_second hpacket, packet.t3b_nominal_secondOpposite hpacket,
    rpow_idealLogLength call.base call.domain.scale _ (commonRadical_ne_zero _ _)]
  cases side <;> simp only [Bool.not_false, Bool.not_true, commonRadical_comm]

/-- The hypotheses are only the two individual bare common-scalar
square bounds. They are discharged by the original frozen atoms. -/
theorem t3bPointScalar_nominal_le
    (input : ProfileInput call) (phases : OriginalPhaseData packet) (side : Bool)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfirst : ∀ s, ‖packet.firstCommonScalar s‖ ^ 2 ≤
      C₁ / (Ideal.absNorm (N4.firstFrozenIdeal packet s) : ℝ))
    (hsecond : ∀ s, ‖(packet.firstAtomTable hpacket phases s).commonScalar
        (packet.secondBranch s)‖ ^ 2 ≤
      C₂ / (Ideal.absNorm (N4.secondFrozenIdeal packet s) : ℝ)) :
    packet.t3bPointScalar hpacket phases side * call.base ^ packet.t3bNominalNorm side ≤
      (C₁ * C₂ * T3b.profileAnnulus c call.frame ^ (4 * c.geometry.slots) * orbitalFieldFactor K) *
        packet.second.physical.first.t3bAllowance *
        call.base ^ (-(call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)) *
        call.base ^ (packet.second.physical.first.tag.movingLength call.base +
          packet.second.physical.first.tag.poolLength (recipeInductionSigma c)) /
        (Ideal.absNorm (commonRadical (packet.secondIdeal false) (packet.secondIdeal true)) : ℝ) *
        call.base ^ (4 * p.tilt *
          (call.node.parameters.n₁ + call.node.parameters.n₂ + call.node.parameters.z)) := by
  let G := packet.nominal side
  let A := G.skeleton.A
  let Cpair := C₁ * C₂ * T3b.profileAnnulus c call.frame ^ (4 * c.geometry.slots)
  have hCpair : 0 ≤ Cpair := by
    dsimp only [Cpair]
    exact mul_nonneg (mul_nonneg hC₁ hC₂)
      (pow_nonneg (zero_le_one.trans (T3b.profileAnnulus_one_le c call.frame)) _)
  have hpair := packet.t3b_paired_commonScalar_scale_le hpacket input phases
    C₁ C₂ hC₁ hC₂ hfirst hsecond
  rw [packet.t3b_secondNorm_product_eq hpacket side] at hpair
  change (‖packet.secondAtomScalar hpacket phases false‖ *
      ‖packet.secondAtomScalar hpacket phases true‖) *
      (Real.sqrt (packet.t3bBeforeScaleProduct hpacket false) *
        Real.sqrt (packet.t3bBeforeScaleProduct hpacket true)) ≤
    Cpair * call.base ^ (-A + 4 * p.tilt * A) / call.base ^ (2 * G.halfSecond) at hpair
  have hrow := packet.t3bRowAmplitude_le_nominal hpacket side
  have hprod := mul_le_mul hpair hrow packet.t3bRowAmplitude_nonneg
    (div_nonneg (mul_nonneg hCpair (Real.rpow_nonneg call.base_pos.le _))
      (Real.rpow_nonneg call.base_pos.le _))
  have hpaid := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod
        (Real.rpow_nonneg call.base_pos.le (G.skeleton.g₂ - G.skeleton.t₂)))
      (Real.rpow_nonneg call.base_pos.le (-packet.t3bRawExponent side)))
    (Real.rpow_nonneg call.base_pos.le (packet.t3bNominalNorm side))
  have hexp :
      (-A + 4 * p.tilt * A) - 2 * G.halfSecond +
          (G.skeleton.Krow + G.skeleton.g) + (G.skeleton.g₂ - G.skeleton.t₂) -
          packet.t3bRawExponent side + packet.t3bNominalNorm side =
        (A + G.skeleton.q + G.skeleton.R + G.skeleton.E - G.skeleton.c + G.boundary) -
          A + G.skeleton.wo + G.tag.poolLength (recipeInductionSigma c) -
          G.secondRadical + 4 * p.tilt * A := by
    dsimp only [t3bRawExponent, t3bNominalNorm, NominalChildGeometry.nominalWidth,
      NominalChildGeometry.nominalRow, NominalChildGeometry.nominalSupport, G, A]
    ring
  calc
    _ = (((‖packet.secondAtomScalar hpacket phases false‖ *
        ‖packet.secondAtomScalar hpacket phases true‖) *
        (Real.sqrt (packet.t3bBeforeScaleProduct hpacket false) *
          Real.sqrt (packet.t3bBeforeScaleProduct hpacket true))) * packet.t3bRowAmplitude) *
        call.base ^ (G.skeleton.g₂ - G.skeleton.t₂) *
        call.base ^ (-packet.t3bRawExponent side) * call.base ^ packet.t3bNominalNorm side := by
      unfold t3bPointScalar t3bRawNormalizer
      ring
    _ ≤ (Cpair * call.base ^ (-A + 4 * p.tilt * A) / call.base ^ (2 * G.halfSecond)) *
        (orbitalFieldFactor K * call.base ^ (G.skeleton.Krow + G.skeleton.g)) *
        call.base ^ (G.skeleton.g₂ - G.skeleton.t₂) *
        call.base ^ (-packet.t3bRawExponent side) * call.base ^ packet.t3bNominalNorm side := hpaid
    _ = (Cpair * orbitalFieldFactor K) * call.base ^
        ((-A + 4 * p.tilt * A) - 2 * G.halfSecond +
          (G.skeleton.Krow + G.skeleton.g) + (G.skeleton.g₂ - G.skeleton.t₂) -
          packet.t3bRawExponent side + packet.t3bNominalNorm side) := by
      simp only [Real.rpow_add call.base_pos, Real.rpow_sub call.base_pos,
        Real.rpow_neg call.base_pos.le]
      ring
    _ = (Cpair * orbitalFieldFactor K) * call.base ^
        ((A + G.skeleton.q + G.skeleton.R + G.skeleton.E - G.skeleton.c + G.boundary) -
          A + G.skeleton.wo + G.tag.poolLength (recipeInductionSigma c) -
          G.secondRadical + 4 * p.tilt * A) := by rw [hexp]
    _ = _ := by
      rw [packet.t3b_firstAllowance_eq_nominal hpacket side,
        ← packet.t3b_secondRadical_rpow hpacket side,
        ← packet.t3b_nominal_tag hpacket side]
      change (Cpair * orbitalFieldFactor K) * call.base ^
          ((A + G.skeleton.q + G.skeleton.R + G.skeleton.E - G.skeleton.c + G.boundary) -
            A + G.skeleton.wo + G.tag.poolLength (recipeInductionSigma c) -
            G.secondRadical + 4 * p.tilt * A) =
        (Cpair * orbitalFieldFactor K) *
          call.base ^ (A + G.skeleton.q + G.skeleton.R + G.skeleton.E - G.skeleton.c + G.boundary) *
          call.base ^ (-A) *
          call.base ^ (G.skeleton.wo + G.tag.poolLength (recipeInductionSigma c)) /
          call.base ^ G.secondRadical * call.base ^ (4 * p.tilt * A)
      simp only [Real.rpow_add call.base_pos, Real.rpow_sub call.base_pos,
        Real.rpow_neg call.base_pos.le]
      ring

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bPointScalar_nominal_le
