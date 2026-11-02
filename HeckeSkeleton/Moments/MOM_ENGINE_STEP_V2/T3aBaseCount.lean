import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aRealization

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original exceptional leaves have only finitely many sixth-free bases

The common original source index and its genuine nonunit class fix the
finite-character multiplier before the row varies. The exceptional test
is then the original parent theta membership test, not a new predicate.
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

namespace RawFamily

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second} (raw : RawFamily geometry)

theorem packet_exceptional_character (j : Fin raw.count) (h : (raw.packet j).R.live) :
    (raw.packet j).leaf.exceptional h.val ↔
      (second.source (raw.index j).val.1.1).rowCharacter
        (expansion := expansion) (raw.index j).val.1.1
        (raw.index j).val.1.2.1 (raw.index j).val.1.2.2.1
        (SourceClassKey.rowLabel (raw.index j).val.1.2) h.val ∈ call.node.data.theta :=
  Iff.rfl

theorem packet_bases_card (j : Fin raw.count) (hpacket : (raw.packet j).Realizes) :
    (raw.packet j).exceptionalBases.card ≤
      call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) := by
  let packet := raw.packet j
  by_cases hrows : packet.exceptionalRows.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hrows
    let preχ : HeckeCharacter K :=
      call.localizedSource.source.recipe.correction *
        ((expansion.moving (raw.index j).val.1.1).append
          (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
            (Arithmetic.context c) packet.R.primes
            packet.R.leftMultiplicity packet.R.rightMultiplicity
            (actualNonunitPattern (Arithmetic.context c) packet.R.primes
              packet.R.leftMultiplicity packet.R.rightMultiplicity
              (packet.R.frequency h₀.val)))).character
    have hmem (h : packet.R.live) (hh : h ∈ packet.exceptionalRows) :
        preχ * completeIdealRowCharacter K
          ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          (probeData K c) (momentRowCharacters K c)
          ((packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c))
          (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal ∈
            call.node.data.theta := by
      have hex := (raw.packet_exceptional_character j h).mp
        (Finset.mem_filter.mp hh).2.1
      simp only [SecondSource.rowCharacter, dif_pos h.property] at hex
      rw [packet.exceptional_pattern_eq hpacket h h₀] at hex
      exact hex
    have hc := T3a.sixthBases_card_le_theta_unitSectors
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (probeData K c) (momentRowCharacters K c) packet.exceptionalRows
      (fun h => HeckeAxiom.exteriorEquiv (Arithmetic.data c)
        (packet.R.extractedRow (Arithmetic.context c) h).ideal)
      (fun h => (packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c))
      preχ call.node.data.theta hmem
    exact hc
  · change (packet.exceptionalRows.image packet.sixthBase).card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hrows, Finset.image_empty, Finset.card_empty]
    exact Nat.zero_le _

end RawFamily

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_bases_card (hpacket : packet.Realizes) :
    packet.exceptionalBases.card ≤
      call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩
  exact raw.packet_bases_card j (raw.packet_realizes trace htrace hgeometry hraw j)

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_bases_card
