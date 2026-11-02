import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N4SixthPattern
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N4: the actual packet supplies its pattern and geometric identities

The witnesses below come from the original source trace and S5 geometry.
The live row is chosen before ordinary-row restriction; an empty ordinary
rectangle therefore introduces no new nonemptiness assumption. A direct
tag forces the actual original zero-slot branch of the same trace.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem packet_live_nonempty (hpacket : packet.Realizes) : Nonempty packet.R.live := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, _, _, rfl⟩
  obtain ⟨h, hh⟩ := (raw.active j).2.2.2
  exact ⟨⟨h, hh⟩⟩

theorem packet_leftMultiplicity_pos : ∀ i, 0 < packet.R.leftMultiplicity i :=
  packet.block.left_positive

theorem packet_rightMultiplicity_pos : ∀ i, 0 < packet.R.rightMultiplicity i :=
  packet.block.right_positive

theorem packet_second_ideal (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.second.val =
      (primePowerProduct packet.R.primes (selectedMultiplicity packet.R side)).val := by
  have hs : (packet.nominal side).ideals.second.val =
      if side then packet.key.1.val.2 else packet.key.1.val.1 := by
    rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
    exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).second side
  cases side
  · exact hs.trans packet.block.common_left.symm
  · exact hs.trans packet.block.common_right.symm

theorem packet_opposite_ideal (hpacket : packet.Realizes) (side : Bool) :
    (packet.nominal side).ideals.secondOpposite.val =
      (primePowerProduct packet.R.primes (oppositeMultiplicity packet.R side)).val := by
  have hs : (packet.nominal side).ideals.secondOpposite.val =
      if side then packet.key.1.val.1 else packet.key.1.val.2 := by
    rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
    exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).secondOpposite side
  cases side
  · exact hs.trans packet.block.common_right.symm
  · exact hs.trans packet.block.common_left.symm

theorem packet_unit_ideal (hpacket : packet.Realizes) (side : Bool) (h : packet.R.live) :
    (packet.nominal side).ideals.unitPart.val =
      (unitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).unitPart side h

theorem packet_nonunit_ideal (hpacket : packet.Realizes) (side : Bool) (h : packet.R.live) :
    (packet.nominal side).ideals.nonunitPart.val =
      (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val)).val := by
  rcases hpacket with ⟨trace, geometry, raw, j, _, hgeometry, _, rfl⟩
  exact (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).nonunitPart side h

theorem packet_unit_pattern (hpacket : packet.Realizes) (side : Bool)
    (pattern : Fin packet.block.primeCount → Bool) (h : packet.R.live)
    (hpattern : actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) = pattern) :
    (packet.nominal side).ideals.unitPart.val =
      (secondPatternUnitIdeal packet.R.primes (selectedMultiplicity packet.R side)
        (oppositeMultiplicity packet.R side) pattern).val :=
  (packet_unit_ideal packet hpacket side h).trans
    (unitIdeal_eq_live packet.R side pattern h hpattern).symm

section Direct

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

/-- A pooled source has a main or an actual error tag. Consequently
only the unchanged direct expansion can carry the direct tag. -/
theorem expansion_direct_parent_zero (expansion : PoolExpansion family)
    (hreal : expansion.Realizes) (i : Fin expansion.count)
    (hdirect : (expansion.source i).first.tag = .direct) :
    call.node.data.geometry.slotCount = 0 := by
  cases expansion with
  | direct => exact hreal
  | pooled pool count index source =>
      change (source i).first.tag = .direct at hdirect
      have horigin := hreal.2.2 i
      cases hindex : (index i).2 with
      | inl unit =>
          simp only [PoolPresentation.Origin, hindex] at horigin
          rcases horigin with ⟨_, _, _, _, _, _, _, hfirst⟩
          have htag : (source i).first.tag = .main :=
            congrArg (fun d : FirstCoordinates call => d.tag) hfirst
          cases hdirect.symm.trans htag
      | inr qe =>
          simp only [PoolPresentation.Origin, hindex] at horigin
          rcases horigin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htag, _, _⟩
          cases hdirect.symm.trans htag

end Direct

theorem packet_direct_parent_zero (hpacket : packet.Realizes) (side : Bool)
    (hdirect : (packet.nominal side).tag = .direct) :
    call.node.data.geometry.slotCount = 0 := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, hgeometry, _, rfl⟩
  have htag := (hgeometry (raw.covers.classKey (raw.index j).val) (raw.active j)).tag side
  have hphysical :
      (trace.second.source (raw.index j).val.1.1).physical.first.tag = .direct :=
    htag.symm.trans hdirect
  rw [htrace.second.physical (raw.index j).val.1.1] at hphysical
  exact expansion_direct_parent_zero trace.expansion htrace.expansion
    (raw.index j).val.1.1 hphysical

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.packet_live_nonempty
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.packet_second_ideal
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.packet_unit_pattern
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N4.packet_direct_parent_zero
