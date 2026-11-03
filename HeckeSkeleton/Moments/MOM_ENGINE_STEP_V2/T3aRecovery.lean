import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aSourceSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationPackets

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Arithmetic recovery on the same original exceptional leaf -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_valuations (hpacket : packet.Realizes)
    (h : packet.R.live) (hh : h ∈ packet.exceptionalRows)
    (i : Fin packet.block.primeCount)
    (hi : i ∈ multiplicityOneNonunitPrimes (Arithmetic.context c)
      packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
      (packet.R.frequency h.val)) :
    6 ∣ (normalizedFactors (packet.R.originalIdeal h.val).val).count
      (packet.R.primes i).val.asIdeal := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  have hp := raw.packet_realizes trace htrace hgeometry hraw j
  exact raw.packet_original_count_dvd_six_of_moving_unramified j h hh i hi
    (RawFamily.packet_moving_unramified trace htrace raw j hp i)

/-- All seven fields concern the unchanged raw leaf and its actual
extracted row. The support identity is exact before integration, and
the fourth-power gain uses the original frequency valuations. -/
theorem exceptional_recovery_of_realizes (hpacket : packet.Realizes) :
    packet.ExceptionalRecovery where
  exact_support := packet.exceptional_exact_support
  bases_card := packet.exceptional_bases_card hpacket
  factorization h _ := packet.exceptional_factorization h
  sixth_free := packet.exceptional_base_sixth_free
  valuations := packet.exceptional_valuations hpacket
  extracted_fibres := packet.exceptional_extracted_fibres hpacket
  fourth_power h hh := packet.exceptional_fourth_power h
    (packet.exceptional_valuations hpacket h hh)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_valuations
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_recovery_of_realizes
