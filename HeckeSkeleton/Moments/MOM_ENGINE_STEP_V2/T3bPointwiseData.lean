import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bScaleCompensation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # The actual scalar normalization of the exceptional source pair -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def t3bNominalNorm (side : Bool) : ℝ :=
  let G := packet.nominal side
  G.skeleton.nominalWidth +
    (G.halfSecond - G.secondRadical + G.skeleton.w + G.boundary +
      G.tag.poolLength (recipeInductionSigma c))

def t3bRawExponent (side : Bool) : ℝ :=
  let G := packet.nominal side
  G.skeleton.A - G.skeleton.c - G.skeleton.w - G.halfSecond

def t3bRawNormalizer (hpacket : packet.Realizes) (side : Bool) : ℝ :=
  Real.sqrt (packet.t3bBeforeScaleProduct hpacket false) *
    Real.sqrt (packet.t3bBeforeScaleProduct hpacket true) *
    call.base ^ (-packet.t3bRawExponent side)

theorem t3bRawNormalizer_nonneg (hpacket : packet.Realizes) (side : Bool) :
    0 ≤ packet.t3bRawNormalizer hpacket side :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg call.base_pos.le _)

def t3bPointScalar (hpacket : packet.Realizes) (phases : OriginalPhaseData packet)
    (side : Bool) : ℝ :=
  ‖packet.secondAtomScalar hpacket phases false‖ *
    ‖packet.secondAtomScalar hpacket phases true‖ * packet.t3bRowAmplitude *
    call.base ^ ((packet.nominal side).skeleton.g₂ - (packet.nominal side).skeleton.t₂) *
    packet.t3bRawNormalizer hpacket side

theorem t3bPointScalar_nonneg (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side : Bool) :
    0 ≤ packet.t3bPointScalar hpacket phases side :=
  mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      packet.t3bRowAmplitude_nonneg) (Real.rpow_nonneg call.base_pos.le _))
    (packet.t3bRawNormalizer_nonneg hpacket side)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint
