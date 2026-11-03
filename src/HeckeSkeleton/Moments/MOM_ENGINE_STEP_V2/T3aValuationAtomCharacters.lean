import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aValuationCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aBaseCount
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bUnscaledAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinarySourceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSupportedVolume

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original unscaled exceptional atoms use the fixed character catalogue

Both signs of the actual second frequency have the same complete
single-ideal coefficient. The unscaled tables retain the original
moving prefix and every coprimality zero. On an exceptional row their
full character is exactly the member of the original parent theta set.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

/-- Reassociate the same appended moving character in an abstract arithmetic context. -/
private theorem character_append_bridge
    {A : SArithmeticData K}
    {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
    {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
    (correction : HeckeCharacter K) (D E : OriginalMovingFactors A P R)
    (χ : HeckeCharacter K) :
    (correction * D.character) * E.character * χ =
      correction * (D.append E).character * χ := by
  simp only [OriginalMovingFactors.append_character, mul_assoc]

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def t3bCompleteMask (phases : OriginalPhaseData packet) (h : packet.R.live) :
    Ideal (𝓞 K) :=
  T3b.completePhaseMask (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal
    (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
      (actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val))).support.val
    (secondSixthRootIdeal packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity)
    (phases.mask false)

theorem t3bCompleteMask_ne_zero (phases : OriginalPhaseData packet) (h : packet.R.live) :
    packet.t3bCompleteMask phases h ≠ 0 :=
  T3b.completePhaseMask_ne_zero _ _
    (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
      (actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val))).support.property.1
    _ _

def t3bOriginalCharacter (phases : OriginalPhaseData packet) (h : packet.R.live) :
    HeckeCharacter K :=
  call.localizedSource.source.recipe.correction *
    ((phases.moving false).append
      (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
        (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
        (actualNonunitPattern (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)))).character *
    completeIdealRowCharacter K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (probeData K c) (momentRowCharacters K c)
      ((packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c))
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal

/-- Both actual source sides retain the same full coefficient. The
right side's negative frequency is handled before its external star. -/
theorem t3bUnscaled_plain_coefficient (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (h : packet.R.live) (side : Bool)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient
        (packet.t3bUnscaledTable hpacket phases side).characters.plain
        (packet.t3bUnscaledTable hpacket phases side).characters.plainTwist
        (packet.t3bUnscaledTable hpacket phases side).characters.mask J *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) J.val
        ((if side then -packet.R.factor (Arithmetic.context c) h.val
          else packet.R.factor (Arithmetic.context c) h.val) *
            (packet.R.extractedRow (Arithmetic.context c) h).element) =
      (if IsCoprime J.val (packet.t3bCompleteMask phases h) then (1 : ℂ) else 0) *
        CanonicalExceptionalVolume.coefficient
          (call.localizedData.plainBackground * packet.t3bOriginalCharacter phases h) J.val := by
  have hroot : (probeData K c).arithmetic.root6 = (Arithmetic.data c).zeta12 ^ 2 := rfl
  have hemb : (probeData K c).arithmetic.embedding = Arithmetic.embedding c := rfl
  have hcharacter := character_append_bridge
    (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
    call.localizedSource.source.recipe.correction (phases.moving false)
    (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
      (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity packet.R.rightMultiplicity
      (actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)))
    (completeIdealRowCharacter K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (probeData K c) (momentRowCharacters K c)
      ((packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c))
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal)
  have hcoefficient := congrArg
    (fun character : HeckeCharacter K =>
      (if IsCoprime J.val (packet.t3bCompleteMask phases h) then (1 : ℂ) else 0) *
        CanonicalExceptionalVolume.coefficient
          (call.localizedData.plainBackground * character) J.val)
    hcharacter
  cases side with
  | false =>
    change sourcePlainCoefficient
        (call.localizedData.plainBackground *
          (call.localizedSource.source.recipe.correction * (phases.moving false).character))
        1 (CanonicalOriginalPhaseCalibration.originalCoprimeMask (phases.mask false)) J *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) J.val
        (packet.R.factor (Arithmetic.context c) h.val *
          (packet.R.extractedRow (Arithmetic.context c) h).element) = _
    have hplain :=
      T3b.extracted_plain_coefficient (probeData K c) (momentRowCharacters K c)
        hroot hemb (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity
        (actualNonunitPattern (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val))
        (packet.R.extractedRow (Arithmetic.context c) h)
        (packet.R.factor_sixth_active (Arithmetic.context c) h.val)
        call.localizedData.plainBackground
        (call.localizedSource.source.recipe.correction * (phases.moving false).character)
        (phases.mask false) J
    exact hplain.trans hcoefficient
  | true =>
    change sourcePlainCoefficient
        (call.localizedData.plainBackground *
          (call.localizedSource.source.recipe.correction * (phases.moving false).character))
        1 (CanonicalOriginalPhaseCalibration.originalCoprimeMask (phases.mask false)) J *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) J.val
        (-packet.R.factor (Arithmetic.context c) h.val *
          (packet.R.extractedRow (Arithmetic.context c) h).element) = _
    have hplain :=
      T3b.extracted_plain_coefficient_neg (probeData K c) (momentRowCharacters K c)
        hroot hemb (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity
        (actualNonunitPattern (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val))
        (packet.R.extractedRow (Arithmetic.context c) h)
        (packet.R.factor_sixth_active (Arithmetic.context c) h.val)
        call.localizedData.plainBackground
        (call.localizedSource.source.recipe.correction * (phases.moving false).character)
        (phases.mask false) J
    exact hplain.trans hcoefficient

end RawLeafPacket

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)

theorem t3bOriginalCharacter_eq_source (j : Fin raw.count) (h : (raw.packet j).R.live) :
    (raw.packet j).t3bOriginalCharacter (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h =
      (trace.second.source (raw.index j).val.1.1).rowCharacter
        (expansion := trace.expansion) (raw.index j).val.1.1
        (raw.index j).val.1.2.1 (raw.index j).val.1.2.2.1
        (SourceClassKey.rowLabel (raw.index j).val.1.2) h.val := by
  have hlive : h.val ∈
      ((trace.second.source (raw.index j).val.1.1).rows
        (raw.index j).val.1.2.1 (raw.index j).val.1.2.2.1
        (SourceClassKey.rowLabel (raw.index j).val.1.2)).live :=
    h.property
  simp only [RawLeafPacket.t3bOriginalCharacter, OrdinaryPhaseFacts.ofRaw_moving_false,
    SecondSource.rowCharacter, dif_pos hlive]
  rfl

/-- The catalogue is fixed by the original target. Only its finite
index is selected from the actual exceptional membership proof. -/
theorem t3b_exceptional_catalogue (j : Fin raw.count) (h : (raw.packet j).R.live)
    (hh : h ∈ (raw.packet j).exceptionalRows) :
    ∃ index : T3b.CharacterIndex c,
      T3b.character c index = call.localizedData.plainBackground *
        (raw.packet j).t3bOriginalCharacter (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h := by
  have hmem := (raw.packet_exceptional_character j h).mp
    (Finset.mem_filter.mp hh).2.1
  have hcanonical :
      (raw.packet j).t3bOriginalCharacter (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h ∈
        Expansion.Project.canonicalDetectorTheta K (targetCharacter K c) := by
    have hparent :
        (raw.packet j).t3bOriginalCharacter (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h ∈
          call.node.data.theta :=
      (congrArg
        (fun χ : HeckeCharacter K => χ ∈ call.node.data.theta)
        (raw.t3bOriginalCharacter_eq_source trace htrace j h)).mpr hmem
    exact (congrArg
      (fun theta : Finset (HeckeCharacter K) =>
        (raw.packet j).t3bOriginalCharacter (OrdinaryPhaseFacts.ofRaw trace htrace raw j) h ∈ theta)
      call.source.source.theta_eq).mp hparent
  obtain ⟨index, hindex⟩ := T3b.character_covers c call.localizedData.plainBackground _
    call.localizedData.plain_background_spec hcanonical false
  refine ⟨index, ?_⟩
  simpa only [Bool.false_eq_true, if_false] using hindex

end RawFamily

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3bUnscaled_plain_coefficient
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.t3b_exceptional_catalogue
